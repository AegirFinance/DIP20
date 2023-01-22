import Array "mo:base/Array";
import Blob "mo:base/Blob";
import Buffer "mo:base/Buffer";
import Error "mo:base/Error";
import Nat8 "mo:base/Nat8";
import Option "mo:base/Option";
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

    public type DecodeError = {
        // Subaccount length is invalid.
        #BadLength;
        // The subaccount encoding is not canonical.
        #NotCanonical;
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

    public func toText(a: Account) : Text {
        switch (a.subaccount) {
            case (null) { Principal.toText(a.owner) };
            case (?blob) {
                assert(blob.size() == 32);
                let shrunk = shrink(blob);
                if (shrunk.size() == 0) {
                    Principal.toText(a.owner)
                } else {
                    let principalBytes = Principal.toBlob(a.owner);
                    let b = Buffer.Buffer<Nat8>(principalBytes.size() + shrunk.size() + 2);
                    for (x in principalBytes.vals()) { b.add(x) };
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

    public func fromText(t: Text) : Result.Result<Account, DecodeError> {
        let principal = Principal.fromText(t);
        let bytes = Blob.toArray(Principal.toBlob(principal));

        if (bytes.size() == 0 or bytes[bytes.size() - 1] != Nat8.fromNat(0x7f)) {
            return #ok({ owner = principal; subaccount = null });
        };

        if (bytes.size() == 1) {
            return #err(#BadLength);
        };

        let n = Nat8.toNat(bytes[bytes.size() - 2]);
        if (n == 0) {
            return #err(#NotCanonical);
        };
        if (n > 32 or bytes.size() < n + 2) {
            return #err(#BadLength);
        };
        if (bytes[bytes.size() - n - 2] == Nat8.fromNat(0)) {
            return #err(#NotCanonical);
        };

        let zeroCount = 32 - n;
        let subaccount = Blob.fromArray(Array.tabulate(32, func(i: Nat) : Nat8 {
            if (i < zeroCount) {
                0
            } else {
                bytes[bytes.size() - n - 2 + i - zeroCount]
            }
        }));

        let owner = Blob.fromArray(Array.tabulate(bytes.size() - n - 2, func(i: Nat) : Nat8 {
            bytes[i]
        }));

        #ok({
            owner = Principal.fromBlob(owner);
            subaccount = ?subaccount;
        })
    };

    public func equal(a: Account, b: Account) : Bool {
        if (not Principal.equal(a.owner, b.owner)) {
            return false;
        };
        let default = defaultSubaccount();
        Blob.equal(
            Option.get(a.subaccount, default),
            Option.get(b.subaccount, default)
        )
    };

    public func hash(a: Account) : Nat32 {
        let subaccount = switch (a.subaccount) {
            case (null) { defaultSubaccount() };
            case (?sub) { sub };
        };
        Principal.hash(a.owner) ^ Blob.hash(subaccount)
    };
};
