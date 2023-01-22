/**
 * Module     : types.mo
 * Copyright  : 2021 DFinance Team
 * License    : Apache 2.0 with LLVM Exception
 * Maintainer : DFinance Team <hello@dfinance.ai>
 * Stability  : Experimental
 */

import Time "mo:base/Time";
import P "mo:base/Prelude";
import Account "./account";

module {
    /// Update call operations
    public type Operation = {
        #mint;
        #burn;
        #transfer;
        #transferFrom;
        #approve;
    };
    public type TransactionStatus = {
        #succeeded;
        #inprogress;
        #failed;
    };
    /// Update call operation record fields
    public type TxRecord = {
        caller: ?Principal;
        op: Operation;
        index: Nat;
        from: Principal;
        to: Principal;
        amount: Nat;
        fee: Nat;
        timestamp: Time.Time;
        status: TransactionStatus;
    };
    public type Transaction = {
        caller: Principal;
        from: Account.Account;
        to: Account.Account;
        amount: Nat;
        fee: ?Nat;
        memo: ?Blob;
        created_at_time: ?Nat64;
    };

    public type TxIndex = Nat;

    public type ICRC1TransferArgs = {
        from_subaccount: ?Account.Subaccount;
        to: Account.Account;
        amount: Nat;
        fee: ?Nat;
        memo: ?Blob;
        created_at_time: ?Nat64;
    };

    public type ICRC1TransferError = {
        #BadFee: { expected_fee: Nat };
        #BadBurn: { min_burn_amount: Nat };
        #InsufficientFunds: { balance: Nat };
        #TooOld;
        #CreatedInFuture: { ledger_time: Nat64 };
        #Duplicate: { duplicate_of: Nat };
        #TemporarilyUnavailable;
        #GenericError: { error_code: Nat; message: Text };
    };

    public type ICRC1TransferResult = {
        #Ok: TxIndex;
        #Err: ICRC1TransferError;
    };

    public func unwrap<T>(x : ?T) : T =
        switch x {
            case null { P.unreachable() };
            case (?x_) { x_ };
        };
};    
