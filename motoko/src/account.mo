/**
 * Module     : account.mo
 * Copyright  : 2021 DFinance Team
 * License    : Apache 2.0 with LLVM Exception
 * Maintainer : DFinance Team <hello@dfinance.ai>
 * Stability  : Experimental
 */

import Array "mo:base/Array";
import Blob "mo:base/Blob";
import Buffer "mo:base/Buffer";
import Error "mo:base/Error";
import Nat8 "mo:base/Nat8";
import P "mo:base/Prelude";
import Principal "mo:base/Principal";
import Result "mo:base/Result";
import Time "mo:base/Time";

module {
    public type Subaccount = Blob;
    public type Account = {
        owner: Principal;
        subaccount: ?Subaccount;
    };

    public func fromPrincipal(owner: Principal, subaccount: ?Subaccount): Account {
        {
            owner = owner;
            subaccount = subaccount;
        }
    };

    public func defaultSubaccount() : Subaccount {
        Blob.fromArrayMut(Array.init(32, 0 : Nat8))
    };

    public func encode(a: Account) : Text {
        switch (a.subaccount) {
            case (null) { Principal.toText(a.owner) };
            case (?s) {
                if (s == defaultSubaccount()) {
                    Principal.toText(a.owner)
                } else {
                    let b = Buffer.Buffer<Nat8>(32);
                    for (x in Principal.toBlob(a.owner).vals()) { b.add(x) };
                    let shrunk = shrink(s);
                    for (x in shrunk.vals()) { b.add(x) };
                    b.add(Nat8.fromNat(shrunk.size()));
                    b.add(0x7F);
                    Principal.toText(
                        Principal.fromBlob(
                            Blob.fromArray(
                                b.toArray()
                            )
                        )
                    )
                }
            };
        }
    };

    // Remove all leading 0-bytes
    func shrink(input: Blob) : Blob {
        let out = Buffer.Buffer<Nat8>(input.size());
        var found = false;
        for (x in input.vals()) {
            if (found or x != 0) {
                found := true;
                out.add(x);
            }
        };
        Blob.fromArray(out.toArray())
    };

    public func decode(t: Text) : Result.Result<Account, Error.Error> {
        // TODO: Implement this
        assert(false);
        loop {};
    };

    public func equal(a: Account, b: Account) : Bool {
        if (not Principal.equal(a.owner, b.owner)) {
            return false;
        };
        switch (a.subaccount, b.subaccount) {
            case (?a_sub, ?b_sub) { Blob.equal(a_sub, b_sub) };
            case (null, null) { true };
            case (_, _) { false };
        }
    };

    public func hash(a: Account) : Nat32 {
        let subaccount = switch (a.subaccount) {
            case (null) { defaultSubaccount() };
            case (?sub) { sub };
        };
        Principal.hash(a.owner) ^ Blob.hash(subaccount)
    };
};
