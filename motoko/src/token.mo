/**
 * Module     : token.mo
 * Copyright  : 2021 DFinance Team
 * License    : Apache 2.0 with LLVM Exception
 * Maintainer : DFinance Team <hello@dfinance.ai>
 * Stability  : Experimental
 */

import Array "mo:base/Array";
import Buffer "mo:base/Buffer";
import ExperimentalCycles "mo:base/ExperimentalCycles";
import HashMap "mo:base/HashMap";
import Int "mo:base/Int";
import Int64 "mo:base/Int64";
import Iter "mo:base/Iter";
import Nat64 "mo:base/Nat64";
import Nat8 "mo:base/Nat8";
import Nat "mo:base/Nat";
import Option "mo:base/Option";
import Order "mo:base/Order";
import Principal "mo:base/Principal";
import Result "mo:base/Result";
import Text "mo:base/Text";
import Time "mo:base/Time";
import Account "./account";
import Cap "./cap/Cap";
import Root "./cap/Root";
import Types "./types";

shared(msg) actor class Token(
    _logo: Text,
    _name: Text,
    _symbol: Text,
    _decimals: Nat8,
    _totalSupply: Nat,
    _owner: Principal,
    _fee: Nat
    ) = this {
    let TX_WINDOW: Int = 86_400_000_000_000; // 24 hours in ns
    let PERMITTED_DRIFT: Int = 120_000_000_000; // 2 minutes in ns

    type UpgradeData = {
        #v1: {
            owner : Principal;
            logo : Text;
            name : Text;
            decimals : Nat8;
            symbol : Text;
            totalSupply : Nat;
            blackhole : Principal;
            feeTo : Account.Account;
            fee : Nat;
            mintingAccount : ?Account.Account;
            balances : [(Account.Account, Nat)];
            allowances : [(Account.Account, [(Principal, Allowance)])];
            duplicates : [{
                index : Types.TxIndex;
                args : {
                    caller: Principal;
                    from: Account.Account;
                    to: Account.Account;
                    amount: Nat;
                    fee: ?Nat;
                    memo: ?Blob;
                    created_at_time: ?Nat64;
                };
            }];
        };
    };
    private stable var upgradeData: ?UpgradeData = null;

    type Operation = Types.Operation;
    type TransactionStatus = Types.TransactionStatus;
    type TxRecord = Types.TxRecord;
    type TxLogEntry = {
        index : Types.TxIndex;
        args : Types.Transaction;
    };
    type TxLog = Buffer.Buffer<TxLogEntry>;
    type Metadata = {
        logo : Text;
        name : Text;
        symbol : Text;
        decimals : Nat8;
        totalSupply : Nat;
        owner : Principal;
        fee : Nat;
    };
    // returns tx index or error msg
    public type TxReceipt = {
        #Ok: Nat;
        #Err: {
            #InsufficientAllowance;
            #InsufficientBalance;
            #ErrorOperationStyle;
            #Unauthorized;
            #LedgerTrap;
            #ErrorTo;
            #Other: Text;
            #BlockUsed;
            #AmountTooSmall;
        };
    };
    public type Allowance = {
        allowance: Nat;
        expires_at: ?Nat64;
    };

    private stable var owner_ : Principal = _owner;
    private stable var logo_ : Text = _logo;
    private stable var name_ : Text = _name;
    private stable var decimals_ : Nat8 = _decimals;
    private stable var symbol_ : Text = _symbol;
    private stable var totalSupply_ : Nat = _totalSupply;
    private stable var blackhole : Principal = Principal.fromText("aaaaa-aa");
    // Deprecated: feeTo
    private stable var feeTo : Principal = owner_;
    private stable var feeToAccount : Account.Account = Account.fromPrincipal(owner_, null);
    private stable var fee : Nat = _fee;
    private stable var mintingAccount : ?Account.Account = null;
    // Deprecated: balanceEntries
    private stable var balanceEntries : [(Principal, Nat)] = [];
    // Deprecated: allowanceEntries
    private stable var allowanceEntries : [(Principal, [(Principal, Nat)])] = [];
    // Deprecated: balances
    private var balances = HashMap.HashMap<Principal, Nat>(1, Principal.equal, Principal.hash);
    // Deprecated: allowances
    private var allowances = HashMap.HashMap<Principal, HashMap.HashMap<Principal, Nat>>(1, Principal.equal, Principal.hash);

    private var accountBalances = HashMap.HashMap<Account.Account, Nat>(1, Account.equal, Account.hash);
    private var accountAllowances = HashMap.HashMap<Account.Account, HashMap.HashMap<Principal, Allowance>>(1, Account.equal, Account.hash);
    private var duplicates = Buffer.Buffer<TxLogEntry>(1024);

    balances.put(owner_, totalSupply_);
    accountBalances.put(Account.fromPrincipal(owner_, null), totalSupply_);

    private stable let genesis : TxRecord = {
        caller = ?owner_;
        op = #mint;
        index = 0;
        from = blackhole;
        to = owner_;
        amount = totalSupply_;
        fee = 0;
        timestamp = Time.now();
        status = #succeeded;
    };
    
    private stable var txcounter: Nat = 0;
    private var cap: ?Cap.Cap = null;
    private func addRecord(
        caller: Principal,
        op: Text, 
        details: [(Text, Root.DetailValue)]
        ): async () {
        let c = switch(cap) {
            case(?c) { c };
            case(_) { Cap.Cap(Principal.fromActor(this), 2_000_000_000_000) };
        };
        cap := ?c;
        let record: Root.IndefiniteEvent = {
            operation = op;
            details = details;
            caller = caller;
        };
        // don't wait for result, faster
        ignore c.insert(record);
    };

    private func _chargeFee(from: Account.Account, fee: Nat) {
        if (fee > 0) {
            _transfer(from, feeToAccount, fee);
        };
    };

    private func _transfer(from: Account.Account, to: Account.Account, value: Nat) {
        let from_balance = _balanceOf(from);
        let from_balance_new : Nat = from_balance - value;
        if (from_balance_new != 0) {
            accountBalances.put(from, from_balance_new);
        } else {
            accountBalances.delete(from);
        };

        let to_balance = _balanceOf(to);
        let to_balance_new : Nat = to_balance + value;
        if (to_balance_new != 0) {
            accountBalances.put(to, to_balance_new);
        } else {
            accountBalances.delete(to);
        };
    };

    private func _updateAllowance(from: Account.Account, spender: Principal, amount: Int, new_expiry: ?Nat64): () {
        let existing = _allowance(from, spender);
        let expires_at = if (Option.isSome(new_expiry)) {
            new_expiry
        } else {
            existing.expires_at
        };
        let allowance = Int.abs(Int.max(existing.allowance + amount, 0));
        let v: Allowance = { allowance; expires_at };
        if (allowance == 0 and Option.isSome(accountAllowances.get(from))) {
            // Clearing the approval
            let allowance_caller = Types.unwrap(accountAllowances.get(from));
            allowance_caller.delete(spender);
            if (allowance_caller.size() == 0) {
                accountAllowances.delete(from);
            } else {
                accountAllowances.put(from, allowance_caller);
            };
        } else if (allowance != 0 and Option.isNull(accountAllowances.get(from))) {
            // Adding a new approval
            var temp = HashMap.HashMap<Principal, Allowance>(1, Principal.equal, Principal.hash);
            temp.put(spender, v);
            accountAllowances.put(from, temp);
        } else if (allowance != 0 and Option.isSome(accountAllowances.get(from))) {
            // Updating the approval
            let allowance_caller = Types.unwrap(accountAllowances.get(from));
            allowance_caller.put(spender, v);
            accountAllowances.put(from, allowance_caller);
        };
    };

    private func _balanceOf(who: Account.Account) : Nat {
        Option.get(accountBalances.get(who), 0)
    };

    private func _allowance(owner: Account.Account, spender: Principal) : Allowance {
        let existing = Option.get(
            Option.chain<HashMap.HashMap<Principal, Allowance>, Allowance>(
                accountAllowances.get(owner),
                func (a) { a.get(spender) }
            ),
            {allowance = 0; expires_at = null}
        );
        switch (existing.expires_at) {
            case (?exp) {
                if (exp < Nat64.fromNat(Int.abs(Time.now() - PERMITTED_DRIFT))) {
                    return {allowance = 0; expires_at = null};
                };
            };
            case (null) { };
        };
        existing
    };

    private func u64(i: Nat): Nat64 {
        Nat64.fromNat(i)
    };

    private func i64(i: Int): Int64 {
        Int64.fromInt(i)
    };


    /*
    *   Core interfaces:
    *       update calls:
    *           transfer/transferFrom/approve
    *       query calls:
    *           logo/name/symbol/decimal/totalSupply/balanceOf/allowance/getMetadata
    *           historySize/getTransaction/getTransactions
    */

    /// Transfers value amount of tokens to Principal to.
    public shared(msg) func transfer(to: Principal, value: Nat) : async TxReceipt {
        let fromAccount = Account.fromPrincipal(msg.caller, null);
        if (_balanceOf(fromAccount) < value + fee) { return #Err(#InsufficientBalance); };
        _chargeFee(fromAccount, fee);
        _transfer(fromAccount, Account.fromPrincipal(to, null), value);
        ignore addRecord(
            msg.caller, "transfer",
            [
                ("to", #Principal(to)),
                ("value", #U64(u64(value))),
                ("fee", #U64(u64(fee)))
            ]
        );
        txcounter += 1;
        return #Ok(txcounter - 1);
    };

    /// Transfers value amount of tokens from Principal from to Principal to.
    public shared(msg) func transferFrom(from: Principal, to: Principal, value: Nat) : async TxReceipt {
        let fromAccount = Account.fromPrincipal(from, null);
        if (_balanceOf(fromAccount) < value + fee) { return #Err(#InsufficientBalance); };
        let allowed = _allowance(fromAccount, msg.caller);
        if (allowed.allowance < value + fee) { return #Err(#InsufficientAllowance); };
        _chargeFee(fromAccount, fee);
        _transfer(fromAccount, Account.fromPrincipal(to, null), value);
        _updateAllowance(fromAccount, msg.caller, -1 * (value + fee), null);
        ignore addRecord(
            msg.caller, "transferFrom",
            [
                ("from", #Principal(from)),
                ("to", #Principal(to)),
                ("value", #U64(u64(value))),
                ("fee", #U64(u64(fee)))
            ]
        );
        txcounter += 1;
        return #Ok(txcounter - 1);
    };

    public type ICRC2TransferFromArgs = {
        from: Account.Account;
        to: Account.Account;
        amount: Nat;
        fee: ?Nat;
        memo: ?Blob;
        created_at_time: ?Nat64;
    };

    public type ICRC2TransferFromError = {
        #BadFee: { expected_fee: Nat };
        #BadBurn: { min_burn_amount: Nat };
        // The [from] account does not hold enough funds for the transfer.
        #InsufficientFunds: { balance: Nat };
        // The caller exceeded its allowance.
        #InsufficientAllowance: { allowance: Nat };
        #TooOld;
        #CreatedInFuture: { ledger_time: Nat64 };
        #Duplicate: { duplicate_of: Nat };
        #TemporarilyUnavailable;
        #GenericError: { error_code: Nat; message: Text };
    };

    public type ICRC2TransferFromResult = {
        #Ok: Nat;
        #Err: ICRC2TransferFromError;
    };

    public shared(msg) func icrc2_transfer_from(args: ICRC2TransferFromArgs) : async ICRC2TransferFromResult {
        let fromAccount = args.from;
        let toAccount = args.to;
        let record: Types.Transaction = {
            caller = msg.caller;
            from = fromAccount;
            to = args.to;
            amount = args.amount;
            fee = args.fee;
            memo = args.memo;
            created_at_time = args.created_at_time;
        };
        switch (dedupeTransaction(record)) {
            case (#ok) {};
            case (#err(e)) { return #Err(e) };
        };

        // Check the allowance
        let allowed = _allowance(fromAccount, msg.caller);
        var feeApplied = fee;

        if (?toAccount == mintingAccount) {
            // This is a burn
            // No fee for burns
            feeApplied := 0;
            if (args.fee != null and args.fee != ?0) {
                return #Err(#BadFee({expected_fee = fee}));
            };
            // Check the balance
            let balance = _balanceOf(fromAccount);
            if (balance < args.amount) {
                return #Err(#InsufficientFunds({balance = balance}));
            };
            if (allowed.allowance < args.amount) { return #Err(#InsufficientAllowance({allowance = allowed.allowance})); };
            totalSupply_ -= args.amount;
            accountBalances.put(fromAccount, balance - args.amount);
            if (Account.equal(fromAccount, {owner = fromAccount.owner; subaccount = null})) {
                // For the default subaccount. Record it, like a DIP-20 txn
                ignore addRecord(
                    msg.caller, "burn",
                    [
                        ("from", #Principal(fromAccount.owner)),
                        ("value", #U64(u64(args.amount))),
                        ("fee", #U64(u64(0)))
                    ]
                );
            };
        } else if (?fromAccount == mintingAccount) {
            // This is a mint
            // No fee for mints
            feeApplied := 0;
            if (args.fee != null and args.fee != ?0) {
                return #Err(#BadFee({expected_fee = fee}));
            };
            if (allowed.allowance < args.amount) { return #Err(#InsufficientAllowance({allowance = allowed.allowance})); };
            let to_balance = _balanceOf(toAccount);
            totalSupply_ += args.amount;
            accountBalances.put(toAccount, to_balance + args.amount);
            if (Account.equal(toAccount, {owner = toAccount.owner; subaccount = null})) {
                // For the default subaccount. Record it, like a DIP-20 txn
                ignore addRecord(
                    msg.caller, "mint",
                    [
                        ("to", #Principal(toAccount.owner)),
                        ("value", #U64(u64(args.amount))),
                        ("fee", #U64(u64(0)))
                    ]
                );
            };
        } else {
            // This is a normal transfer
            if (args.fee != null and args.fee != ?fee) {
                return #Err(#BadFee({expected_fee = fee}));
            };
            let balance = _balanceOf(fromAccount);
            if (balance < args.amount + fee) {
                return #Err(#InsufficientFunds({balance = balance}));
            };
            if (allowed.allowance < args.amount) { return #Err(#InsufficientAllowance({allowance = allowed.allowance})); };
            _chargeFee(fromAccount, fee);
            _transfer(fromAccount, args.to, args.amount);
            if (Account.equal(args.to, {owner = args.to.owner; subaccount = null})) {
                // For the default subaccount. Record it, like a DIP-20 txn
                ignore addRecord(
                    msg.caller, "transfer",
                    [
                        ("to", #Principal(args.to.owner)),
                        ("value", #U64(u64(args.amount))),
                        ("fee", #U64(u64(fee)))
                    ]
                );
            };
        };

        _updateAllowance(fromAccount, msg.caller, -1 * (args.amount + feeApplied), null);

        txcounter += 1;
        duplicates := logTransaction(txcounter, record, duplicates);
        return #Ok(txcounter - 1);
    };

    /// Allows spender to withdraw from your account multiple times, up to the value amount.
    /// If this function is called again it overwrites the current allowance with value.
    public shared(msg) func approve(spender: Principal, value: Nat) : async TxReceipt {
        let fromAccount = Account.fromPrincipal(msg.caller, null);
        if (spender == msg.caller) {
            return #Err(#Other("Caller cannot equal spender"));
        };
        if (_balanceOf(fromAccount) < fee) {
            return #Err(#InsufficientBalance);
        };
        _chargeFee(fromAccount, fee);

        // dip-20 approve resets the allowed amount, not incr/decrements. So
        // clear any allowance first. This will incidentally clear the expiry.
        let existing = _allowance(fromAccount, spender);
        if (existing.allowance > 0) {
            _updateAllowance(fromAccount, spender, -1 * existing.allowance, null);
        };
        _updateAllowance(fromAccount, spender, value, null);
        ignore addRecord(
            msg.caller, "approve",
            [
                ("to", #Principal(spender)),
                ("value", #U64(u64(value))),
                ("fee", #U64(u64(fee)))
            ]
        );
        txcounter += 1;
        return #Ok(txcounter - 1);
    };

    public type ICRC2ApproveArgs = {
        from_subaccount: ?Blob;
        spender: Principal;
        amount: Int;
        expires_at: ?Nat64;
        fee: ?Nat;
        memo: ?Blob;
        created_at_time: ?Nat64;
    };

    public type ICRC2ApproveError = {
        #BadFee: { expected_fee: Nat };
        // The caller does not have enough funds to pay the approval fee.
        #InsufficientFunds: { balance: Nat };
        // The approval request expired before the ledger had a chance to apply it.
        #Expired: { ledger_time: Nat64; };
        #TooOld;
        #CreatedInFuture: { ledger_time: Nat64 };
        #Duplicate: { duplicate_of: Nat };
        #TemporarilyUnavailable;
        #GenericError: { error_code: Nat; message: Text };
    };

    public type ICRC2ApproveResult = {
        #Ok: Nat;
        #Err: ICRC2ApproveError;
    };

    public shared(msg) func icrc2_approve(args: ICRC2ApproveArgs) : async ICRC2ApproveResult {
        let fromAccount = Account.fromPrincipal(msg.caller, args.from_subaccount);
        if (args.spender == msg.caller) {
            return #Err(#GenericError({error_code = 1; message = "Caller cannot equal spender"}));
        };
        if (args.fee != null and args.fee != ?fee) {
            return #Err(#BadFee({expected_fee = fee}));
        };
        let balance = _balanceOf(fromAccount);
        if (balance < fee) {
            return #Err(#InsufficientFunds({balance = balance}));
        };
        let ledger_time = Nat64.fromNat(Int.abs(Time.now()));
        switch (args.expires_at) {
            case (?e) {
                if (e < ledger_time - Nat64.fromNat(Int.abs(PERMITTED_DRIFT))) {
                    return #Err(#Expired({ ledger_time }));
                };
            };
            case (_) { };
        };
        _chargeFee(fromAccount, fee);
        _updateAllowance(fromAccount, args.spender, args.amount, args.expires_at);
        ignore addRecord(
            msg.caller, "approve",
            [
                ("to", #Principal(args.spender)),
                ("value", #I64(i64(args.amount))),
                ("fee", #U64(u64(fee)))
            ]
        );
        txcounter += 1;
        return #Ok(txcounter - 1);
    };

    public shared(msg) func mint(to: Principal, value: Nat): async TxReceipt {
        if (msg.caller != owner_) {
            return #Err(#Unauthorized);
        };
        let toAccount = Account.fromPrincipal(to, null);
        let to_balance = _balanceOf(toAccount);
        totalSupply_ += value;
        accountBalances.put(toAccount, to_balance + value);
        ignore addRecord(
            msg.caller, "mint",
            [
                ("to", #Principal(to)),
                ("value", #U64(u64(value))),
                ("fee", #U64(u64(0)))
            ]
        );
        txcounter += 1;
        return #Ok(txcounter - 1);
    };

    public shared(msg) func mintAll(mints: [(Principal, Nat)]): async TxReceipt {
        if (msg.caller != owner_) {
            return #Err(#Unauthorized);
        };
        for ((to, value) in mints.vals()) {
            let toAccount = Account.fromPrincipal(to, null);
            let to_balance = _balanceOf(toAccount);
            totalSupply_ += value;
            accountBalances.put(toAccount, to_balance + value);
            ignore addRecord(
                msg.caller, "mint",
                [
                    ("to", #Principal(to)),
                    ("value", #U64(u64(value))),
                    ("fee", #U64(u64(0)))
                ]
            );
            txcounter += 1;
        };
        return #Ok(mints.size());
    };

    public shared(msg) func mintAllAccounts(mints: [(Account.Account, Nat)]): async Types.ICRC1TransferResult {
        if (msg.caller != owner_) {
            return #Err(#GenericError({error_code = 0; message = "Unauthorized"}));
        };
        for ((to, value) in mints.vals()) {
            let balance = _balanceOf(to);
            totalSupply_ += value;
            accountBalances.put(to, balance + value);
            ignore addRecord(
                msg.caller, "mint",
                [
                    ("to", #Principal(to.owner)),
                    ("value", #U64(u64(value))),
                    ("fee", #U64(u64(0)))
                ]
            );
            txcounter += 1;
        };
        return #Ok(mints.size());
    };

    public shared(msg) func burnFor(user: Principal, amount: Nat): async TxReceipt {
        if (msg.caller != owner_ and msg.caller != user) {
            return #Err(#Unauthorized);
        };
        let fromAccount = Account.fromPrincipal(user, null);
        let from_balance = _balanceOf(fromAccount);
        if (from_balance < amount) {
            return #Err(#InsufficientBalance);
        };
        totalSupply_ -= amount;
        accountBalances.put(fromAccount, from_balance - amount);
        ignore addRecord(
            user, "burn",
            [
                ("from", #Principal(user)),
                ("value", #U64(u64(amount))),
                ("fee", #U64(u64(0)))
            ]
        );
        txcounter += 1;
        return #Ok(txcounter - 1);
    };

    public shared(msg) func burnForAccount(fromAccount: Account.Account, amount: Nat): async TxReceipt {
        if (msg.caller != owner_ and msg.caller != fromAccount.owner) {
            return #Err(#Unauthorized);
        };
        let from_balance = _balanceOf(fromAccount);
        if (from_balance < amount) {
            return #Err(#InsufficientBalance);
        };
        totalSupply_ -= amount;
        accountBalances.put(fromAccount, from_balance - amount);
        ignore addRecord(
            fromAccount.owner, "burn",
            [
                ("from", #Principal(fromAccount.owner)),
                ("value", #U64(u64(amount))),
                ("fee", #U64(u64(0)))
            ]
        );
        txcounter += 1;
        return #Ok(txcounter - 1);
    };

    public shared(msg) func burn(amount: Nat): async TxReceipt {
        let fromAccount = Account.fromPrincipal(msg.caller, null);
        let from_balance = _balanceOf(fromAccount);
        if (from_balance < amount) {
            return #Err(#InsufficientBalance);
        };
        totalSupply_ -= amount;
        accountBalances.put(fromAccount, from_balance - amount);
        ignore addRecord(
            msg.caller, "burn",
            [
                ("from", #Principal(msg.caller)),
                ("value", #U64(u64(amount))),
                ("fee", #U64(u64(0)))
            ]
        );
        txcounter += 1;
        return #Ok(txcounter - 1);
    };

    public query func logo() : async Text {
        return logo_;
    };

    public query func name() : async Text {
        return name_;
    };

    public query func symbol() : async Text {
        return symbol_;
    };

    public query func decimals() : async Nat8 {
        return decimals_;
    };

    public query func totalSupply() : async Nat {
        return totalSupply_;
    };

    public query func getTokenFee() : async Nat {
        return fee;
    };

    public query func balanceOf(who: Principal) : async Nat {
        return _balanceOf(Account.fromPrincipal(who, null));
    };

    public query func allowance(owner: Principal, spender: Principal) : async Nat {
        return _allowance(Account.fromPrincipal(owner, null), spender).allowance;
    };

    public type ICRC2AllowanceArgs = {
        account: Account.Account;
        spender: Principal;
    };

    public query func icrc2_allowance(args: ICRC2AllowanceArgs) : async Allowance {
        return _allowance(args.account, args.spender);
    };

    public query func getMetadata() : async Metadata {
        return {
            logo = logo_;
            name = name_;
            symbol = symbol_;
            decimals = decimals_;
            totalSupply = totalSupply_;
            owner = owner_;
            fee = fee;
        };
    };

    /// Get transaction history size
    public query func historySize() : async Nat {
        return txcounter;
    };

    /*
    *   Optional interfaces:
    *       setName/setLogo/setFee/setFeeTo/setOwner
    *       getUserTransactionsAmount/getUserTransactions
    *       getTokenInfo/getHolders/getUserApprovals
    */
    public shared(msg) func setName(name: Text) {
        assert(msg.caller == owner_);
        name_ := name;
    };

    public shared(msg) func setLogo(logo: Text) {
        assert(msg.caller == owner_);
        logo_ := logo;
    };

    public shared(msg) func setFeeTo(to: Principal) {
        assert(msg.caller == owner_);
        feeTo := to;
        feeToAccount := Account.fromPrincipal(to, null);
    };

    public shared(msg) func setFee(_fee: Nat) {
        assert(msg.caller == owner_);
        fee := _fee;
    };

    public shared(msg) func setOwner(_owner: Principal) {
        assert(msg.caller == owner_);
        owner_ := _owner;
    };

    public shared(msg) func setMintingAccount(_mintingAccount: ?Account.Account) : async () {
        assert(msg.caller == owner_);
        mintingAccount := _mintingAccount;
    };

    public type TokenInfo = {
        metadata: Metadata;
        feeTo: Principal;
        // status info
        historySize: Nat;
        deployTime: Time.Time;
        holderNumber: Nat;
        cycles: Nat;
    };
    public query func getTokenInfo(): async TokenInfo {
        {
            metadata = {
                logo = logo_;
                name = name_;
                symbol = symbol_;
                decimals = decimals_;
                totalSupply = totalSupply_;
                owner = owner_;
                fee = fee;
            };
            // TODO: Bit of a backwards-compatibility hack with dip-20
            feeTo = feeToAccount.owner;
            historySize = txcounter;
            deployTime = genesis.timestamp;
            holderNumber = accountBalances.size();
            cycles = ExperimentalCycles.balance();
        }
    };

    public query func getHolders(start: Nat, limit: Nat) : async [(Principal, Nat)] {
        let temp =  Iter.toArray(accountBalances.entries());
        func onlyPrincipals ((account, balance): (Account.Account, Nat)) : ?(Principal, Nat) {
            if (Account.equal(account, {owner=account.owner; subaccount=null})) {
                ?(account.owner, balance)
            } else {
                null
            }
        };
        let filtered = Array.mapFilter(temp, onlyPrincipals);
        func order (a: (Principal, Nat), b: (Principal, Nat)) : Order.Order {
            return Nat.compare(b.1, a.1);
        };
        let sorted = Array.sort(filtered, order);
        let limit_: Nat = if (start + limit > temp.size()) {
            temp.size() - start
        } else {
            limit
        };
        let res = Array.init<(Principal, Nat)>(limit_, (owner_, 0));
        for (i in Iter.range(0, limit_ - 1)) {
            res[i] := sorted[i+start];
        };
        return Array.freeze(res);
    };

    public query func getHolderAccounts(start: Nat, limit: Nat) : async [(Account.Account, Nat)] {
        let temp =  Iter.toArray(accountBalances.entries());
        func order (a: (Account.Account, Nat), b: (Account.Account, Nat)) : Order.Order {
            return Nat.compare(b.1, a.1);
        };
        let sorted = Array.sort(temp, order);
        let limit_: Nat = if (limit == 0) {
            temp.size() - start
        } else if (start + limit > temp.size()) {
            temp.size() - start
        } else {
            limit
        };
        let res = Array.init<(Account.Account, Nat)>(limit_, (Account.fromPrincipal(owner_, null), 0));
        for (i in Iter.range(0, limit_ - 1)) {
            res[i] := sorted[i+start];
        };
        return Array.freeze(res);
    };

    public query func getAllowanceSize() : async Nat {
        var size : Nat = 0;
        for ((k, v) in accountAllowances.entries()) {
            size += v.size();
        };
        return size;
    };

    public query func getUserApprovals(who : Principal) : async [(Principal, Allowance)] {
        switch (accountAllowances.get(Account.fromPrincipal(who, null))) {
            case (?allowance_who) {
                return Iter.toArray(allowance_who.entries());
            };
            case (_) {
                return [];
            };
        }
    };

    /*
    * ICRC-1 Implementation Methods
    * https://github.com/dfinity/ICRC-1/blob/main/standards/ICRC-1/README.md
    */

    public query func icrc1_name() : async Text {
        return name_;
    };

    public query func icrc1_symbol() : async Text {
        return symbol_;
    };

    public query func icrc1_decimals() : async Nat8 {
        return decimals_;
    };

    public query func icrc1_fee() : async Nat {
        return fee;
    };

    public type ICRC1MetadataValue = {
        #Nat: Nat;
        #Int: Int;
        #Text: Text;
        #Blob: Blob;
    };

    public query func icrc1_metadata() : async [(Text, ICRC1MetadataValue)] {
        [
            ("icrc1:symbol", #Text(symbol_)),
            ("icrc1:name", #Text(name_)),
            ("icrc1:decimals", #Nat(Nat8.toNat(decimals_))),
            ("icrc1:fee", #Nat(fee)),
        ]
    };

    public query func icrc1_total_supply() : async Nat {
        return totalSupply_;
    };


    public query func icrc1_minting_account() : async ?Account.Account {
        return mintingAccount;
    };

    public query func icrc1_balance_of(account: Account.Account) : async Nat {
        return _balanceOf(account);
    };

    public shared(msg) func icrc1_transfer(args: Types.ICRC1TransferArgs) : async Types.ICRC1TransferResult {
        let fromAccount = Account.fromPrincipal(msg.caller, args.from_subaccount);
        let toAccount = args.to;
        let record: Types.Transaction = {
            caller = msg.caller;
            from = fromAccount;
            to = args.to;
            amount = args.amount;
            fee = args.fee;
            memo = args.memo;
            created_at_time = args.created_at_time;
        };
        switch (dedupeTransaction(record)) {
            case (#ok) {};
            case (#err(e)) { return #Err(e) };
        };
        if (?toAccount == mintingAccount) {
            // This is a burn
            // No fee for burns
            if (args.fee != null and args.fee != ?0) {
                return #Err(#BadFee({expected_fee = fee}));
            };
            // Check the balance
            let balance = _balanceOf(fromAccount);
            if (balance < args.amount) {
                return #Err(#InsufficientFunds({balance = balance}));
            };
            totalSupply_ -= args.amount;
            accountBalances.put(fromAccount, balance - args.amount);
            if (Account.equal(fromAccount, {owner = fromAccount.owner; subaccount = null})) {
                // For the default subaccount. Record it, like a DIP-20 txn
                ignore addRecord(
                    msg.caller, "burn",
                    [
                        ("from", #Principal(msg.caller)),
                        ("value", #U64(u64(args.amount))),
                        ("fee", #U64(u64(0)))
                    ]
                );
            };
        } else if (?fromAccount == mintingAccount) {
            // This is a mint
            // No fee for mints
            if (args.fee != null and args.fee != ?0) {
                return #Err(#BadFee({expected_fee = fee}));
            };
            let to_balance = _balanceOf(toAccount);
            totalSupply_ += args.amount;
            accountBalances.put(toAccount, to_balance + args.amount);
            if (Account.equal(toAccount, {owner = toAccount.owner; subaccount = null})) {
                // For the default subaccount. Record it, like a DIP-20 txn
                ignore addRecord(
                    msg.caller, "mint",
                    [
                        ("to", #Principal(toAccount.owner)),
                        ("value", #U64(u64(args.amount))),
                        ("fee", #U64(u64(0)))
                    ]
                );
            };
        } else {
            // This is a normal transfer
            if (args.fee != null and args.fee != ?fee) {
                return #Err(#BadFee({expected_fee = fee}));
            };
            let balance = _balanceOf(fromAccount);
            if (balance < args.amount + fee) {
                return #Err(#InsufficientFunds({balance = balance}));
            };
            _chargeFee(fromAccount, fee);
            _transfer(fromAccount, args.to, args.amount);
            if (Account.equal(args.to, {owner = args.to.owner; subaccount = null})) {
                // For the default subaccount. Record it, like a DIP-20 txn
                ignore addRecord(
                    msg.caller, "transfer",
                    [
                        ("to", #Principal(args.to.owner)),
                        ("value", #U64(u64(args.amount))),
                        ("fee", #U64(u64(fee)))
                    ]
                );
            };
        };
        txcounter += 1;
        duplicates := logTransaction(txcounter, record, duplicates);
        return #Ok(txcounter - 1);
    };

    func dedupeTransaction(args: Types.Transaction) : Result.Result<(), Types.ICRC1TransferError> {
        switch (args.created_at_time) {
            case (null) {};
            case (?t) {
                let ledger_time = Nat64.fromNat(Int.abs(Time.now()));
                if (t < ledger_time - Nat64.fromNat(Int.abs(TX_WINDOW + PERMITTED_DRIFT))) {
                    return #err(#TooOld);
                };
                if (ledger_time + Nat64.fromNat(Int.abs(PERMITTED_DRIFT)) < t) {
                    return #err(#CreatedInFuture({ledger_time = ledger_time}));
                };
                switch (findTransaction(args, duplicates)) {
                    case (null) {};
                    case (?duplicate_of) {
                        return #err(#Duplicate({duplicate_of}));
                    };
                };
            };
        };
        #ok(())
    };

    func findTransaction(args: Types.Transaction, log: TxLog): ?Types.TxIndex {
        for (tx in log.vals()) {
            if (args == tx.args) {
                return ?tx.index;
            };
        };
        null
    };

    // pruneTransactionLog removes transactions which have drifted outside the
    // sliding window of retained transactions.
    func pruneTransactionLog(log: TxLog): TxLog {
        let cutoff = Nat64.fromNat(Int.abs(Time.now() - TX_WINDOW - PERMITTED_DRIFT));
        let newLog = Buffer.Buffer<TxLogEntry>(log.size());
        for (entry in log.vals()) {
            // Preserve all the entries after the cutoff
            if (cutoff < Option.get(entry.args.created_at_time, 0: Nat64)) {
                newLog.add(entry);
            };
        };
        newLog
    };

    func logTransaction(index: Types.TxIndex, args: Types.Transaction, log: TxLog): TxLog {
        // Only prune the transaction log when logging a successful transaction, because at this point the user has paid the fee.
        let newLog = pruneTransactionLog(log);
        newLog.add({index; args});
        newLog
    };

    public type ICRC1Standard = {
        name: Text;
        url: Text;
    };

    public query func icrc1_supported_standards(a: Account.Account) : async [ICRC1Standard] {
        [
            { name = "ICRC-1"; url = "https://github.com/dfinity/ICRC-1" },
            { name = "ICRC-2"; url = "https://github.com/dfinity/ICRC-2" },
            { name = "DIP-20"; url = "https://github.com/Psychedelic/DIP20" }
        ]
    };

    /*
    * upgrade functions
    */
    system func preupgrade() {
        var allowancesTemp = Buffer.Buffer<(Account.Account, [(Principal, Allowance)])>(accountAllowances.size());
        for ((k, v) in accountAllowances.entries()) {
            allowancesTemp.add((k, Iter.toArray(v.entries())));
        };

        upgradeData := ?#v1({
            owner = owner_;
            logo = logo_;
            name = name_;
            decimals = decimals_;
            symbol = symbol_;
            totalSupply = totalSupply_;
            blackhole = blackhole;
            feeTo = feeToAccount;
            fee = fee;
            mintingAccount = mintingAccount;
            balances = Iter.toArray(accountBalances.entries());
            allowances = allowancesTemp.toArray();
            duplicates = duplicates.toArray();
        });
    };

    system func postupgrade() {
        switch (upgradeData) {
            case (null) {
                // Initial upgrade to this version, convert from previous
                // DIP-20 stable storage

                // Convert balances to account balances
                accountBalances := HashMap.HashMap<Account.Account, Nat>(
                    balanceEntries.size(),
                    Account.equal,
                    Account.hash
                );
                for ((k, v) in balanceEntries.vals()) {
                    accountBalances.put(Account.fromPrincipal(k, null), v);
                };
                balanceEntries := [];

                // Convert allowances to account allowances
                accountAllowances := HashMap.HashMap<Account.Account, HashMap.HashMap<Principal, Allowance>>(
                    allowanceEntries.size(),
                    Account.equal,
                    Account.hash
                );
                for ((k, v) in allowanceEntries.vals()) {
                    let allowed_temp = HashMap.HashMap<Principal, Allowance>(v.size(), Principal.equal, Principal.hash);
                    for ((principal, allowance) in v.vals()) {
                        allowed_temp.put(principal, {allowance = allowance; expires_at = null});
                    };
                    accountAllowances.put(Account.fromPrincipal(k, null), allowed_temp);
                };
                allowanceEntries := [];
            };
            case (?#v1(data)) {
                // Normal update
                owner_ := data.owner;
                logo_ := data.logo;
                name_ := data.name;
                decimals_ := data.decimals;
                symbol_ := data.symbol;
                totalSupply_ := data.totalSupply;
                blackhole := data.blackhole;
                feeToAccount := data.feeTo;
                fee := data.fee;
                mintingAccount := data.mintingAccount;

                accountBalances := HashMap.fromIter<Account.Account, Nat>(
                    data.balances.vals(),
                    data.balances.size(),
                    Account.equal,
                    Account.hash
                );

                accountAllowances := HashMap.HashMap<Account.Account, HashMap.HashMap<Principal, Allowance>>(
                    data.allowances.size(),
                    Account.equal,
                    Account.hash
                );
                for ((k, v) in data.allowances.vals()) {
                    accountAllowances.put(
                        k,
                        HashMap.fromIter<Principal, Allowance>(
                            v.vals(),
                            v.size(),
                            Principal.equal,
                            Principal.hash
                        )
                    );
                };

                duplicates.clear();
                for (tx in data.duplicates.vals()) {
                    duplicates.add(tx);
                };

                upgradeData := null;
            };
        };
    };
};
