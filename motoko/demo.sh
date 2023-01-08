#!/bin/bash

# set -e

function cleanup() {
    dfx stop
}

trap cleanup EXIT

# clear
dfx stop
rm -rf .dfx
mkdir .dfx

ALICE_HOME=./tmp/alice
BOB_HOME=./tmp/bob
DAN_HOME=./tmp/dan
FEE_HOME=./tmp/fee
MINT_HOME=./tmp/fee
HOME=$ALICE_HOME

for dir in $ALICE_HOME $BOB_HOME $DAN_HOME $FEE_HOME $MINT_HOME; do
    mkdir -p $dir
done

ALICE_PUBLIC_KEY="principal \"$( \
    HOME=$ALICE_HOME dfx identity get-principal
)\""
ALICE_ACCOUNT="record {owner=$ALICE_PUBLIC_KEY}"
ALICE_SUBACCOUNT="record {owner=$ALICE_PUBLIC_KEY; subaccount=opt vec {1}}"

BOB_PUBLIC_KEY="principal \"$( \
    HOME=$BOB_HOME dfx identity get-principal
)\""
BOB_ACCOUNT="record {owner=$BOB_PUBLIC_KEY}"

DAN_PUBLIC_KEY="principal \"$( \
    HOME=$DAN_HOME dfx identity get-principal
)\""
DAN_ACCOUNT="record {owner=$DAN_PUBLIC_KEY}"

FEE_PUBLIC_KEY="principal \"$( \
    HOME=$FEE_HOME dfx identity get-principal
)\""
FEE_ACCOUNT="record {owner=$FEE_PUBLIC_KEY}"

MINT_PUBLIC_KEY="principal \"$( \
    HOME=$MINT_HOME dfx identity get-principal
)\""
MINT_ACCOUNT="record {owner=$MINT_PUBLIC_KEY}"

echo Alice id = $ALICE_PUBLIC_KEY
echo Bob id = $BOB_PUBLIC_KEY
echo Dan id = $DAN_PUBLIC_KEY
echo Fee id = $FEE_PUBLIC_KEY
echo Mint id = $MINT_PUBLIC_KEY

dfx start --clean --background
dfx canister create --no-wallet token
dfx build

TOKENID=$(dfx canister id token)
TOKENID="principal \"$TOKENID\""

echo Token id: $TOKENID

echo
echo == Install token canister
echo

HOME=$ALICE_HOME
eval dfx canister install token --argument="'(\"Test Token Logo\", \"Test Token Name\", \"Test Token Symbol\", 3, 1000000, $ALICE_PUBLIC_KEY, 0)'"

call() {
eval dfx canister call token "$@"
}

echo
echo == Initial setting for token canister
echo

call setFeeTo "'($FEE_PUBLIC_KEY)'"
call setFee "'(100)'"
call setMintingAccount "'(opt $MINT_ACCOUNT)'"

echo
echo == Initial token balances for Alice and Bob, Dan, FeeTo
echo

balances() {
echo Alice = $( \
    call icrc1_balance_of "'($ALICE_ACCOUNT)'" \
)
echo Alice_subaccount = $( \
    call icrc1_balance_of "'($ALICE_SUBACCOUNT)'" \
)
echo Bob = $( \
    call icrc1_balance_of "'($BOB_ACCOUNT)'" \
)
echo Dan = $( \
    call icrc1_balance_of "'($DAN_ACCOUNT)'" \
)
echo FeeTo = $( \
    call icrc1_balance_of "'($FEE_ACCOUNT)'" \
)
}
balances

echo
echo == Mint 0 tokens to Bob, should succeed
echo

HOME=$MINT_HOME
call icrc1_transfer "'(record {to=$BOB_ACCOUNT; amount=0})'"

echo
echo == Mint 10 tokens to Bob, should succeed
echo

HOME=$MINT_HOME
call icrc1_transfer "'(record {to=$BOB_ACCOUNT; amount=10_000})'"

echo
echo == Burn 10 tokens from Bob, should succeed
echo

HOME=$BOB_HOME
call icrc1_transfer "'(record {to=$MINT_ACCOUNT; amount=10_000})'"

echo
echo == Burn 10 tokens from Bob, should fail with insufficient funds
echo

HOME=$BOB_HOME
call icrc1_transfer "'(record {to=$MINT_ACCOUNT; amount=10_000})'"

echo
echo == Transfer 0.1 tokens from Alice to Bob, should success, revieve 0, as value = fee.
echo

HOME=$ALICE_HOME
call icrc1_transfer "'(record {to=$BOB_ACCOUNT; amount=100})'"

echo
echo == Transfer 0.1 tokens from Alice to Alice, should success, revieve 0, as value = fee.
echo

call icrc1_transfer "'(record {to=$ALICE_ACCOUNT; amount=100})'"

echo
echo == Transfer 100 tokens from Alice to Alice, should success.
echo

call icrc1_transfer "'(record {to=$ALICE_ACCOUNT; amount=100_000})'"

echo
echo == Transfer 2000 tokens from Alice to Alice, should Return false, as no enough balance.
echo

call icrc1_transfer "'(record {to=$ALICE_ACCOUNT; amount=2_000_000})'"

echo
echo == Transfer 0 tokens from Bob to Bob, should Return false, as value is smaller than fee.
echo

HOME=$BOB_HOME
call icrc1_transfer "'(record {to=$BOB_ACCOUNT; amount=0})'"

echo
echo == Transfer 42 tokens from Alice to Bob, should success.
echo

HOME=$ALICE_HOME
call icrc1_transfer "'(record {to=$BOB_ACCOUNT; amount=42_000})'"

echo
echo == Transfer 69 tokens from Alice to a subaccount, should success.
echo

HOME=$ALICE_HOME
call icrc1_transfer "'(record {to=$ALICE_SUBACCOUNT; amount=69_000})'"

echo
echo == Transfer 11 tokens from Alice subaccount to Bob, should success.
echo

HOME=$ALICE_HOME
call icrc1_transfer "'(record {from_subaccount=opt vec {1}; to=$BOB_ACCOUNT; amount=11_000})'"

echo
echo == Alice grants Dan permission to spend 1 of her tokens, should success.
echo

call icrc2_approve "'(record {spender=$DAN_PUBLIC_KEY; amount=1_000})'"

echo
echo == Alice revokes Dans permission to spend her tokens, should success.
echo

call icrc2_approve "'(record {spender=$DAN_PUBLIC_KEY; amount=-1_000})'"

echo
echo == Alices allowances
echo

alices_allowances() {
    echo Alices allowance for Bob = $( \
        call icrc2_allowance "'(record {account=$ALICE_ACCOUNT; spender=$BOB_PUBLIC_KEY})'" \
    )
    echo Alices allowance for Dan = $( \
        call icrc2_allowance "'(record {account=$ALICE_ACCOUNT; spender=$DAN_PUBLIC_KEY})'" \
    )
}

alices_allowances

echo
echo == Bob grants Dan permission to spend 1 of her tokens, should success.
echo

HOME=$BOB_HOME
call icrc2_approve "'(record {spender=$DAN_PUBLIC_KEY; amount=1_000})'"

echo
echo == Dan transfer 1 token from Bob to Alice, should success.
echo

HOME=$DAN_HOME
call icrc2_transfer_from "'(record {from=$BOB_ACCOUNT; to=$ALICE_ACCOUNT; amount=1_000})'"


echo
echo == Transfer 40.9 tokens from Bob to Alice, should success.
echo

HOME=$BOB_HOME
call icrc1_transfer "'(record {to=$ALICE_ACCOUNT; amount=40_900})'"

echo
echo == token balances for Alice, Bob, Dan and FeeTo.
echo

balances

echo
echo == Alice grants Dan permission to spend 50 of her tokens, should success.
echo

HOME=$ALICE_HOME
call icrc2_approve "'(record {spender=$DAN_PUBLIC_KEY; amount=50_000})'"

echo
echo == Alices allowances 
echo

alices_allowances

echo
echo == Dan transfers 40 tokens from Alice to Bob, should success.
echo

HOME=$DAN_HOME
call icrc2_transfer_from "'(record {from=$ALICE_ACCOUNT; to=$BOB_ACCOUNT; amount=40_000})'"

echo
echo == Alice transfer 1 tokens To Dan
echo

HOME=$ALICE_HOME
call icrc1_transfer "'(record {to=$DAN_ACCOUNT; amount=1_000})'"

echo
echo == Dan transfers 40 tokens from Alice to Bob, should Return false, as allowance remain 10, smaller than 40.
echo

HOME=$DAN_HOME
call icrc2_transfer_from "'(record {from=$ALICE_ACCOUNT; to=$BOB_ACCOUNT; amount=40_000})'"

echo
echo == Token balance for Alice and Bob and Dan
echo

balances

echo
echo == Alices allowances
echo

alices_allowances

echo
echo == Alice grants Bob permission to spend 100 of her tokens
echo

HOME=$ALICE_HOME
call icrc2_approve "'(record {spender=$BOB_PUBLIC_KEY; amount=100_000})'"

echo
echo == Alices allowances
echo

alices_allowances

echo
echo == Bob transfers 99 tokens from Alice to Dan
echo

HOME=$BOB_HOME
call icrc2_transfer_from "'(record {from=$ALICE_ACCOUNT; to=$DAN_ACCOUNT; amount=99_000})'"

echo
echo == Balances
echo

balances

echo
echo == Alices allowances
echo

alices_allowances

echo
echo == Dan grants Bob permission to spend 100 of this tokens, should success.
echo

HOME=$DAN_HOME
call icrc2_approve "'(record {spender=$BOB_PUBLIC_KEY; amount=100_000})'"

echo
echo == Dan lowers Bob permission to spend 50 of this tokens
echo

call icrc2_approve "'(record {spender=$BOB_PUBLIC_KEY; amount=-50_000})'"

echo
echo == Dan allowances
echo

echo Dan allowance for Alice = $( \
    call icrc2_allowance "'(record {account=$DAN_ACCOUNT; spender=$ALICE_PUBLIC_KEY})'" \
)
echo Dan allowance for Bob = $( \
    call icrc2_allowance "'(record {account=$DAN_ACCOUNT; spender=$BOB_PUBLIC_KEY})'" \
)

echo
echo == Dan change Bobs permission to spend 40 of this tokens instead of 50
echo

call icrc2_approve "'(record {spender=$BOB_PUBLIC_KEY; amount=-10_000})'"

echo
echo == Dan allowances
echo

echo Dan allowance for Alice = $( \
    call icrc2_allowance "'(record {account=$DAN_ACCOUNT; spender=$ALICE_PUBLIC_KEY})'" \
)
echo Dan allowance for Bob = $( \
    call icrc2_allowance "'(record {account=$DAN_ACCOUNT; spender=$BOB_PUBLIC_KEY})'" \
)

echo
echo == logo
echo
call logo

echo
echo == name
echo
call icrc1_name

echo
echo == symbol
echo
call icrc1_symbol

echo
echo == decimals
echo
call icrc1_decimals

echo
echo == totalSupply
echo
call icrc1_total_supply

echo
echo == getMetadata
echo
call icrc1_metadata

echo
echo == historySize
echo
call historySize

echo
echo == getTransaction
echo
call getTransaction "'(1)'"

echo
echo == getTransactions
echo
call getTransactions "'(0,100)'" 

echo
echo == getUserTransactionAmount
echo
eval dfx canister  call token getUserTransactionAmount "'($ALICE_PUBLIC_KEY)'" 

echo
echo == getUserTransactions
echo
call getUserTransactions "'($ALICE_PUBLIC_KEY, 0, 1000)'"

echo
echo == getTokenInfo
echo
eval dfx canister  call token getTokenInfo

echo
echo == getHolderAccounts
echo
eval dfx canister  call token getHolderAccounts "'(0,100)'"

echo
echo == getAllowanceSize
echo
eval dfx canister  call token getAllowanceSize

echo
echo == getUserApprovals
echo
eval dfx canister  call token getUserApprovals "'($ALICE_PUBLIC_KEY)'"

echo
echo == get alice getUserTransactions
echo
eval dfx canister  call token getUserTransactions "'($ALICE_PUBLIC_KEY, 0, 1000)'"

echo
echo == get bob History
echo
eval dfx canister  call token getUserTransactions "'($BOB_PUBLIC_KEY, 0, 1000)'"

echo
echo == get dan History
echo
eval dfx canister  call token getUserTransactions "'($DAN_PUBLIC_KEY, 0, 1000)'"

echo
echo == get fee History
echo
eval dfx canister  call token getUserTransactions "'($FEE_PUBLIC_KEY, 0, 1000)'"


echo
echo == Upgrade token
echo
HOME=$ALICE_HOME
eval dfx canister install token --argument="'(\"test\", \"Test Token\", \"TT\", 2, 100, $ALICE_PUBLIC_KEY, 100)'" -m=upgrade

echo
echo == all History
echo
call getTransactions "'(0, 1000)'"

echo
echo == getTokenInfo
echo
dfx canister call token getTokenInfo

echo
echo == get alice History
echo
call getUserTransactions "'($ALICE_PUBLIC_KEY, 0, 1000)'"
