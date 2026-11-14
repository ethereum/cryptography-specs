module

public import EthLib.Execution.Proofs.Transactions.Unfold
public import EthLib.Execution.Rpc.Call
import ToMathlib.Data.ByteArray
import EthLib.Execution.Proofs.State.Frame
public import EthLib.Execution.Proofs.Rpc.Raw

/-!
# Proofs: `eth_call`

A call answers data exactly when the message that it prepares ends without an error.

The data is then the output of that message.

A call answers the revert error exactly when that message reverts.

The data of the error is then the output of the revert.

The message runs on the state after the block that the request names.

Its caller is the sender, its target the recipient, and its value that of the request.

A call to a recipient carries the input of the request as its data.

A request that names no fee takes no wei from its sender before its message runs.

Such a request, from a sender that holds its value, never fails with code 809, insufficient funds.

A sender that holds less than the value never gets an answer with data.

A request makes a transaction exactly when it passes the checks below.

Its fee, access, blob and authorization fields must fit its kind.

Its kind must be at most 4, and a request of type 3 or 4 must name a recipient.

A chain that it names must be that of the node.

Each number that the transaction carries must also fit in 256 bits.

That transaction has the kind, the value, the recipient, the data and the lists of the request.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.JsonRpc (RpcError)
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)
open EthLib.Execution.Transactions

/-- A number too large for its field fails with the code of invalid parameters. -/
private theorem callWord_error {what : String} {n : Nat} {e : RpcError}
    (h : callWord what n = .error e) : e.code = -32602 := by
  unfold callWord at h
  split at h <;> cases h
  rfl

/-- A failed check of a parameter has the code of invalid parameters. -/
private theorem ensure_param {condition : Prop} [Decidable condition] {reason : String}
    {e : RpcError} (h : ensure condition (callParamError reason) = .error e) :
    e.code = -32602 := by
  rw [eq_of_ensure_eq_error h]
  rfl

/-- A request that makes no transaction fails with the code of invalid parameters. -/
private theorem toTransaction_error {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {e : RpcError}
    (h : tx.toTransaction chainId nonce gas maxFee = .error e) : e.code = -32602 := by
  unfold GenericTransaction.toTransaction at h
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, reduceCtorEq,
    Except.error.injEq] at h
  all_goals subst h
  all_goals first
    | exact callWord_error (by assumption)
    | exact ensure_param (by assumption)
    | rfl

/-- A number that fits its field keeps its value. -/
private theorem callWord_ok {what : String} {n : Nat} {x : U256}
    (h : callWord what n = .ok x) : x.toNat = n := by
  unfold callWord at h
  split at h <;> cases h
  exact Nat.mod_eq_of_lt ‹_›

/-- A number that fits its field is below `2 ^ 256`. -/
private theorem lt_of_callWord_ok {what : String} {n : Nat} {x : U256}
    (h : callWord what n = .ok x) : n < 2 ^ 256 :=
  callWord_ok h ▸ x.isLt

/-- A kind of at most 4 is one of the five types. -/
private theorem kind_cases {k : UInt8} (h : k ≤ 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
  rw [UInt8.le_iff_toNat_le] at h
  simp only [← UInt8.toNat_inj]
  simp at h ⊢
  omega

/-- A kind of at most 4 that is none of the first four types is type 4. -/
private theorem kind_eq_four {k : UInt8} (h : k ≤ 4) (h0 : ¬k = 0) (h1 : ¬k = 1) (h2 : ¬k = 2)
    (h3 : ¬k = 3) : k = 4 := by
  rcases kind_cases h with rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- A request makes a transaction exactly when it passes each check below.

Its kind is at most 4.

A fee cap or a priority fee needs type 2 or more, and a gas price type 1 or less.

An access list needs type 1 or more, and authorizations type 4.

Blob hashes or a blob fee cap need type 3.

A chain that the request names is the chain of the node.

Type 3 and type 4 need a recipient.

The nonce, the gas limit and the fee cap that the call gives are below `2 ^ 256`.

So is each number of the request that the transaction carries. -/
theorem exists_toTransaction_eq_ok_iff {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} :
    (∃ t, tx.toTransaction chainId nonce gas maxFee = .ok t) ↔
      tx.kind ≤ 4 ∧
      (tx.kind ≤ 1 → tx.maxFeePerGas = none ∧ tx.maxPriorityFeePerGas = none) ∧
      (2 ≤ tx.kind → tx.gasPrice = none) ∧
      (tx.kind = 0 → tx.accessList = none) ∧
      (tx.kind ≠ 3 → tx.blobVersionedHashes = none ∧ tx.maxFeePerBlobGas = none) ∧
      (tx.kind ≠ 4 → tx.authorizationList = none) ∧
      (∀ c, tx.chainId = some c → c = chainId.toNat) ∧
      (3 ≤ tx.kind → tx.to.isSome) ∧
      nonce < 2 ^ 256 ∧ gas < 2 ^ 256 ∧ tx.value.getD 0 < 2 ^ 256 ∧
      tx.maxPriorityFeePerGas.getD 0 < 2 ^ 256 ∧ maxFee < 2 ^ 256 ∧
      tx.gasPrice.getD 0 < 2 ^ 256 ∧ tx.maxFeePerBlobGas.getD 0 < 2 ^ 256 := by
  constructor
  · rintro ⟨t, h⟩
    unfold GenericTransaction.toTransaction at h
    simp only [bind, Except.bind] at h
    repeat' (split at h)
    all_goals simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, reduceCtorEq,
      Except.ok.injEq] at h
    all_goals
      have := lt_of_callWord_ok (what := "nonce") (by assumption)
      have := lt_of_callWord_ok (what := "gas") (by assumption)
      have := lt_of_callWord_ok (what := "value") (by assumption)
      have := lt_of_callWord_ok (what := "maxPriorityFeePerGas") (by assumption)
      have := lt_of_callWord_ok (what := "maxFeePerGas") (by assumption)
      have := lt_of_callWord_ok (what := "gasPrice") (by assumption)
      try have := lt_of_callWord_ok (what := "maxFeePerBlobGas") (by assumption)
      simp only [ensure_ok_iff] at *
    all_goals simp_all
    -- Only type 4 is left, which no branch names by its number.
    all_goals
      have := kind_eq_four ‹tx.kind ≤ 4› ‹¬tx.kind = 0› ‹¬tx.kind = 1› ‹¬tx.kind = 2›
        ‹¬tx.kind = 3›
      simp_all
  · rintro ⟨hk, h1, h2, h3, h4, h5, h6, h7, hn, hg, hv, hp, hm, hgp, hb⟩
    unfold GenericTransaction.toTransaction
    rcases kind_cases hk with hk' | hk' | hk' | hk' | hk' <;>
    rcases hc : tx.chainId with _ | c <;>
    rcases hto : tx.to with _ | to <;>
    simp_all [ensure, callWord, bind, Except.bind, pure, Except.pure]

/-- The fields of the transaction of a request, all at once, for the lemmas below. -/
private theorem toTransaction_fields {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.type = tx.kind ∧ t.nonce.toNat = nonce ∧ t.gas.toNat = gas ∧
      t.value.toNat = tx.value.getD 0 ∧ t.to = tx.to ∧ t.data = tx.input.getD .empty ∧
      t.accesses = tx.accessList.getD [] ∧ t.authorizations = tx.authorizationList.getD [] ∧
      t.blobHashes = tx.blobVersionedHashes.getD [] ∧
      t.maxFeePerGas = (if tx.kind ≤ 1 then tx.gasPrice.getD 0 else maxFee) ∧
      t.maxFeePerBlobGas = tx.maxFeePerBlobGas.getD 0 ∧
      (∀ baseFee, effectiveGasPrice baseFee t = if tx.kind ≤ 1 then tx.gasPrice.getD 0 else
        min (tx.maxPriorityFeePerGas.getD 0) (maxFee - baseFee) + baseFee) ∧
      (1 ≤ tx.kind → ∀ fork, t.chainId fork = .ok (some (.ofNat 256 chainId.toNat))) ∧
      t.unsigned = t := by
  unfold GenericTransaction.toTransaction at h
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, reduceCtorEq,
    Except.ok.injEq] at h
  all_goals subst h
  all_goals
    have := callWord_ok (what := "nonce") (by assumption)
    have := callWord_ok (what := "gas") (by assumption)
    have := callWord_ok (what := "value") (by assumption)
    have := callWord_ok (what := "maxPriorityFeePerGas") (by assumption)
    have := callWord_ok (what := "maxFeePerGas") (by assumption)
    have := callWord_ok (what := "gasPrice") (by assumption)
    try have := callWord_ok (what := "maxFeePerBlobGas") (by assumption)
    simp only [ensure_ok_iff] at *
  all_goals simp_all [Transaction.type, Transaction.nonce, Transaction.gas, Transaction.value,
    Transaction.to, Transaction.data, Transaction.accesses, Transaction.authorizations,
    Transaction.blobHashes, Transaction.maxFeePerGas, Transaction.maxFeePerBlobGas,
    effectiveGasPrice, effectiveGasPrice.feeMarket, Transaction.chainId, Transaction.unsigned]
  -- Only type 4 is left, which no branch names by its number.
  all_goals
    have := kind_eq_four ‹tx.kind ≤ 4› ‹¬tx.kind = 0› ‹¬tx.kind = 1› ‹¬tx.kind = 2›
      ‹¬tx.kind = 3›
    simp_all

/-- The transaction of a request has the kind of the request. -/
theorem type_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.type = tx.kind :=
  (toTransaction_fields h).1

/-- The transaction of a request has the nonce that the call gives. -/
theorem nonce_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.nonce.toNat = nonce :=
  (toTransaction_fields h).2.1

/-- The transaction of a request has the gas limit that the call gives. -/
theorem gas_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.gas.toNat = gas :=
  (toTransaction_fields h).2.2.1

/-- The transaction of a request has the value of the request, or 0. -/
theorem value_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.value.toNat = tx.value.getD 0 :=
  (toTransaction_fields h).2.2.2.1

/-- The transaction of a request has the recipient of the request. -/
theorem to_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.to = tx.to :=
  (toTransaction_fields h).2.2.2.2.1

/-- The transaction of a request has the input of the request, or no data. -/
theorem data_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.data = tx.input.getD .empty :=
  (toTransaction_fields h).2.2.2.2.2.1

/-- The transaction of a request has the access list of the request, or none. -/
theorem accesses_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.accesses = tx.accessList.getD [] :=
  (toTransaction_fields h).2.2.2.2.2.2.1

/-- The transaction of a request has the authorizations of the request, or none. -/
theorem authorizations_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.authorizations = tx.authorizationList.getD [] :=
  (toTransaction_fields h).2.2.2.2.2.2.2.1

/-- The transaction of a request has the blob hashes of the request, or none. -/
theorem blobHashes_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.blobHashes = tx.blobVersionedHashes.getD [] :=
  (toTransaction_fields h).2.2.2.2.2.2.2.2.1

/-- The fee cap of the transaction is the gas price of the request, or 0, up to type 1.

From type 2 it is the cap that the call gives, not the one that the request names. -/
theorem maxFeePerGas_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.maxFeePerGas = if tx.kind ≤ 1 then tx.gasPrice.getD 0 else maxFee :=
  (toTransaction_fields h).2.2.2.2.2.2.2.2.2.1

/-- The blob fee cap of the transaction is that of the request, or 0. -/
theorem maxFeePerBlobGas_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.maxFeePerBlobGas = tx.maxFeePerBlobGas.getD 0 :=
  (toTransaction_fields h).2.2.2.2.2.2.2.2.2.2.1

/-- The price per gas of the transaction is the gas price of the request up to type 1.

From type 2 it is the base fee plus the priority fee of the request.

That priority fee is cut to the fee cap minus the base fee, or to 0 below the base fee. -/
theorem effectiveGasPrice_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    ∀ baseFee, effectiveGasPrice baseFee t = if tx.kind ≤ 1 then tx.gasPrice.getD 0 else
      min (tx.maxPriorityFeePerGas.getD 0) (maxFee - baseFee) + baseFee :=
  (toTransaction_fields h).2.2.2.2.2.2.2.2.2.2.2.1

/-- From type 1, the transaction of a request names the chain of the node at every fork. -/
theorem chainId_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    1 ≤ tx.kind → ∀ fork, t.chainId fork = .ok (some (.ofNat 256 chainId.toNat)) :=
  (toTransaction_fields h).2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The transaction of a request has a signature of 0. -/
theorem unsigned_of_toTransaction_eq_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.unsigned = t :=
  (toTransaction_fields h).2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The transaction of a request keeps its value, its recipient and its data. -/
private theorem toTransaction_ok {tx : GenericTransaction} {chainId : UInt64}
    {nonce gas maxFee : Nat} {t : Transaction}
    (h : tx.toTransaction chainId nonce gas maxFee = .ok t) :
    t.value.toNat = tx.value.getD 0 ∧ t.to = tx.to ∧ t.data = tx.input.getD .empty :=
  ⟨value_of_toTransaction_eq_ok h, to_of_toTransaction_eq_ok h, data_of_toTransaction_eq_ok h⟩

/-- What an error of the setup is not.

It never has the revert code.

With no fee, it has the code of the balance failure only on a block that `p` names.

The sender then holds less than the value, after that block. -/
private def SetupError (v : ChainView) (tx : GenericTransaction) (p : BlockParam)
    (c : CallChoices) (e : RpcError) : Prop :=
  e.code ≠ 3 ∧ (tx.namesFee = false → e.code = insufficientFunds.code →
    ∃ r, v.resolve p = .ok (some r) ∧
      (r.account (tx.sender.getD c.sender)).balance.toNat < tx.value.getD 0)

/-- An error whose code is neither 3 nor 809 is an error of the setup. -/
private theorem setupError_of_code {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} {e : RpcError} {k : Int} (h : e.code = k) (h3 : k ≠ 3) (h809 : k ≠ 809) :
    SetupError v tx p c e :=
  ⟨h ▸ h3, fun _ he => (h809 (h.symm.trans he)).elim⟩

/-- The revert error determines the output of the revert. -/
private theorem revertError_inj {a b : ByteArray} (h : revertError a = revertError b) :
    a = b := by
  have hd := congrArg (fun e : RpcError => e.data) h
  simp only [revertError, Serialization.JsonRpc.dataJson, Option.some.injEq] at hd
  have hl : a.toList = b.toList := by
    have h2 := congrArg (Serialization.JsonRpc.bytes "") hd
    rw [Serialization.JsonRpc.bytes_hexString, Serialization.JsonRpc.bytes_hexString,
      Except.ok.injEq] at h2
    exact List.toByteArray_inj.mp h2
  rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data] at hl
  cases a; cases b
  simp only [Array.toList_inj] at hl
  rw [hl]

/-- No halt answers code 3 or code 809. -/
private theorem haltError_code (e : EvmError) :
    (haltError e).code ≠ 3 ∧ (haltError e).code ≠ 809 := by
  unfold haltError
  split <;> decide

/-- A failed check fails because its condition does not hold. -/
private theorem not_of_ensure_eq_error {c : Prop} [Decidable c] {err e : RpcError}
    (h : ensure c err = .error e) : ¬c := fun hc => by
  simp [ensure, hc] at h

/-- Buying the gas keeps the block of the transaction. -/
private theorem buyGas_parent {fork : Fork} {env : BlockEnvironment fork}
    {st st' : TransactionState} {a : Address} {t : Transaction}
    (h : buyGas env st a t = .ok st') : st'.parent = st.parent := by
  unfold buyGas at h
  rw [paidBaseFee_empty] at h
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  rw [State.TransactionState.parent_modifyState h2,
    State.TransactionState.parent_incrementNonce h1]

/-- Taking the nonce, and the fee when one is named, fails only when a fee is named. -/
private theorem bought_error {b : Bool} {fork fork' : Fork} {env : BlockEnvironment fork'}
    {st : TransactionState} {a : Address} {t : Transaction} {g : State.StateError → RpcError}
    {e : RpcError}
    (h : (if b = true then buyGas env st a t else st.incrementNonce fork a).mapError g =
      .error e) :
    b = true ∧ ∃ s, g s = e := by
  obtain ⟨s, hs, rfl⟩ := mapError_eq_error h
  split at hs
  · exact ⟨‹_›, s, rfl⟩
  · obtain ⟨st', hok⟩ := State.TransactionState.incrementNonce_isOk fork st a
    rw [hok] at hs
    cases hs

/-- Taking the nonce, and the fee when one is named, keeps the block of the transaction.

With no fee, it keeps the balance of the sender. -/
private theorem bought_ok {b : Bool} {fork fork' : Fork} {env : BlockEnvironment fork'}
    {st st' : TransactionState} {a : Address} {t : Transaction}
    {g : State.StateError → RpcError}
    (h : (if b = true then buyGas env st a t else st.incrementNonce fork a).mapError g =
      .ok st') :
    st'.parent = st.parent ∧
      (b = false → (st'.getAccount a).balance = (st.getAccount a).balance) := by
  have h := mapError_ok_iff.mp h
  split at h
  · exact ⟨buyGas_parent h, by simp_all⟩
  · refine ⟨State.TransactionState.parent_incrementNonce h, fun _ => ?_⟩
    rw [(State.TransactionState.getAccount_incrementNonce h).1]

/-- A transaction with no write yet reads the accounts of the state after the block. -/
private theorem getAccount_ofBlock {r : BlockRecord} {a : Address} :
    (TransactionState.ofBlock ⟨r.state, ∅, ∅, ∅, ∅⟩).getAccount a = r.account a := by
  simp [TransactionState.getAccount, TransactionState.getAccountOptional,
    TransactionState.ofBlock, BlockRecord.account]

/-- The message of a transaction comes from the sender at depth 0, to the recipient.

It carries the value of the transaction, and the data of a call to a recipient. -/
private theorem transactionMessage_ok {fork : Fork} {env : BlockEnvironment fork}
    {txEnv : TransactionEnvironment fork} {st : TransactionState} {sender target : Address}
    {gas : Nat} {t : Transaction} {m : Message fork}
    (h : transactionMessage env txEnv st sender target gas t = .ok m) :
    m.caller = sender ∧ m.target = t.to ∧ m.depth = 0 ∧ m.value = t.value ∧
      (t.to.isSome → m.data = t.data) := by
  unfold transactionMessage at h
  split at h
  · obtain ⟨_, -, rfl⟩ := map_ok_iff.mp h
    simp_all
  · cases h
    simp_all

/-- The first message of a transaction comes from the sender at depth 0, to the recipient.

It carries the value of the transaction, and the data of a call to a recipient. -/
private theorem transactionStart_ok {fork : Fork} {env : BlockEnvironment fork}
    {st : TransactionState} {sender target : Address} {price intrinsic : Nat} {t : Transaction}
    {ms : Message fork × Substate}
    (h : transactionStart env st sender target price intrinsic t = .ok ms) :
    ms.1.caller = sender ∧ ms.1.target = t.to ∧ ms.1.depth = 0 ∧ ms.1.value = t.value ∧
      (t.to.isSome → ms.1.data = t.data) := by
  unfold transactionStart at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · cases h
    obtain ⟨h1, h2, h3, h4, h5⟩ := transactionMessage_ok ‹_›
    exact ⟨h1, h2, h3, h4, h5⟩

/-- A transaction runs the message that `transactionStart` builds, once it has bought its gas.

So the call and the transaction build their message by the same steps. -/
theorem runTransaction_eq_transactionStart {fork : Fork} (Meter : Type) [GasMeter Meter]
    [LawfulGasMeter Meter] (env : BlockEnvironment fork) (block : BlockState)
    (included : Included) (tx : Transaction) :
    runTransaction Meter env block included tx = (do
      let state := TransactionState.ofBlock block
      let sender := included.sender
      let target ← messageTarget sender (state.getAccount sender).nonce tx
      let state ← (buyGas env state sender tx).mapError .state
      let (message, substate) ←
        transactionStart env state sender target included.gasPrice included.intrinsicGas tx
      let output ← processMessageCall (Meter := Meter) env.chainId.toNat message state substate
        tx.authorizations (paidWrites sender target tx)
      let gasLeft := output.gasLeft + output.reservoir
      let blockGas := transactionBlockGas fork sender tx gasLeft output.refund output.stateGasUsed
      let gasBeforeRefund := gasUsed fork sender tx gasLeft 0
      let (state, gasUsed) ←
        (settleGas env output.state sender tx gasLeft output.refund).mapError .state
      let state ← (deleteAccounts fork state output).mapError .state
      return ⟨state, gasUsed, blockGas, output.logs, output.simulatedLogs, output.error,
        output.output, gasBeforeRefund⟩) := by
  rw [runTransaction_unfold]
  unfold transactionStart
  simp only [bind_assoc, pure_bind]

namespace ChainView

/-- A block parameter fails only for a block that is not canonical, code -32000. -/
private theorem resolve_error {v : ChainView} {p : BlockParam} {e : RpcError}
    (h : v.resolve p = .error e) : e.code = -32000 := by
  unfold resolve at h
  split at h
  · cases h
  · cases h
  · split at h
    · cases h
    · split at h <;> cases h
      rfl

/-- A setup that fails never answers the revert code.

With no fee, it fails for the balance only when the sender holds less than the value. -/
private theorem prepareCall_error {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} {e : RpcError} (h : v.prepareCall tx p c = .error e) :
    SetupError v tx p c e := by
  unfold prepareCall ofBlock at h
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, reduceCtorEq,
    Except.error.injEq] at h
  all_goals subst h
  all_goals first
    | exact setupError_of_code (resolve_error (by assumption)) (by decide) (by decide)
    | exact setupError_of_code (k := -32001) rfl (by decide) (by decide)
    | exact setupError_of_code (toTransaction_error (by assumption)) (by decide) (by decide)
    | obtain ⟨_, -, rfl⟩ := mapError_eq_error (by assumption)
      exact setupError_of_code rfl (by decide) (by decide)
    | exact setupError_of_code (congrArg RpcError.code (eq_of_ensure_eq_error (by assumption)))
        (by decide) (by decide)
    | -- Only a named fee can fail for the balance while it is paid.
      obtain ⟨hb, s, rfl⟩ := bought_error (by assumption)
      refine ⟨?_, fun hf => absurd hb (by simp [hf])⟩
      cases s <;>
        simp [callInternalError, internalError, insufficientFunds, ErrorCode.toRpcError]
    | -- A value check fails only when the sender holds less than the value.
      have hn := not_of_ensure_eq_error
        (by assumption : ensure _ insufficientFunds.toRpcError = .error _)
      obtain rfl := eq_of_ensure_eq_error
        (by assumption : ensure _ insufficientFunds.toRpcError = .error _)
      refine ⟨by decide, fun hf _ => ⟨_, by assumption, ?_⟩⟩
      obtain ⟨hval, -, -⟩ := toTransaction_ok (by assumption)
      first
        | rw [(bought_ok (by assumption)).2 hf] at hn
        | skip
      rw [getAccount_ofBlock, hval] at hn
      omega

/-- What a call ready to run holds.

It holds the state after the block, the sender and its message.

The balance of its sender covers the value. -/
private theorem prepareCall_ok {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} {s : CallSetup} (h : v.prepareCall tx p c = .ok s) :
    ∃ r, v.resolve p = .ok (some r) ∧ s.state.parent = ⟨r.state, ∅, ∅, ∅, ∅⟩ ∧
      s.sender = tx.sender.getD c.sender ∧ s.message.caller = s.sender ∧
      s.message.target = tx.to ∧ s.message.depth = 0 ∧
      s.message.value.toNat = tx.value.getD 0 ∧
      (tx.to.isSome → s.message.data = tx.input.getD .empty) ∧
      tx.value.getD 0 ≤ (r.account (tx.sender.getD c.sender)).balance.toNat := by
  obtain ⟨r, hr, h⟩ := ofBlock_eq_ok.mp h
  refine ⟨r, hr, ?_⟩
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals simp only [pure, Except.pure, reduceCtorEq, Except.ok.injEq] at h
  all_goals subst h
  all_goals
    obtain ⟨hval, hto, hdata⟩ := toTransaction_ok (by assumption)
    obtain ⟨hcaller, htarget, hdepth, hvalue, hmdata⟩ :=
      transactionStart_ok (mapError_ok_iff.mp (by assumption))
    have hbal := ensure_ok_iff.mp (by assumption : ensure
      (_ ≤ ((TransactionState.ofBlock _).getAccount _).balance.toNat)
      insufficientFunds.toRpcError = .ok _)
    refine ⟨?_, rfl, hcaller, htarget.trans hto, hdepth, hvalue ▸ hval,
      fun h => (hmdata (hto ▸ h)).trans hdata, ?_⟩
    · rw [(bought_ok (by assumption)).1]
      rfl
    · rw [getAccount_ofBlock] at hbal
      omega

/-- The request with the gas limit of its prepared call prepares the same call. -/
theorem prepareCall_gas_self {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} {s : CallSetup} (h : v.prepareCall tx p c = .ok s) :
    v.prepareCall { tx with gas := some s.transaction.gas.toNat } p c = .ok s := by
  obtain ⟨r, hr, hb⟩ := ofBlock_eq_ok.mp h
  refine ofBlock_eq_ok.mpr ⟨r, hr, ?_⟩
  have hg : s.transaction.gas.toNat = tx.gas.getD (c.gasLimit.getD
      (if tx.namesFee then (c.environment v r).env
        else { (c.environment v r).env with baseFeePerGas := fun _ => 0 }).gasLimit) := by
    simp only [bind, Except.bind] at hb
    repeat' (split at hb)
    all_goals simp only [pure, Except.pure, reduceCtorEq, Except.ok.injEq] at hb
    all_goals subst hb
    all_goals exact gas_of_toTransaction_eq_ok (by assumption)
  rw [hg]
  exact hb

/-- The request with the gas limit of its prepared call runs the same call. -/
theorem runCall_gas_self {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} {s : CallSetup} (h : v.prepareCall tx p c = .ok s) :
    v.runCall { tx with gas := some s.transaction.gas.toNat } p c = v.runCall tx p c := by
  unfold runCall
  rw [prepareCall_gas_self h, h]

/-- A call prepares, runs its message, and answers from the output of that message. -/
private theorem ethCall_eq {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} :
    v.ethCall tx p c = (do
      let s ← v.prepareCall tx p c
      let o ← s.run.mapError fun _ => callInternalError "the execution aborted"
      callAnswer o) := by
  unfold ethCall runCall
  rcases v.prepareCall tx p c with e | s <;> simp only [bind, Except.bind]
  rcases s.run with e | o <;> rfl

/-- A call gives a setup and an output exactly when it prepares and its message runs to them. -/
theorem runCall_eq_ok {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} {s : CallSetup} {o : Transactions.CallOutput} :
    v.runCall tx p c = .ok (s, o) ↔ v.prepareCall tx p c = .ok s ∧ s.run = .ok o := by
  unfold runCall
  rcases v.prepareCall tx p c with e | s' <;> simp [bind, Except.bind]
  rcases hrun : s'.run with e | o' <;> simp [Except.mapError, pure, Except.pure]
  all_goals rintro rfl
  all_goals simp [hrun]

/-- A call answers the data `out` exactly when its message ends without an error.

The output of the message is then `out`. -/
theorem ethCall_eq_ok_iff {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} {out : ByteArray} :
    v.ethCall tx p c = .ok out ↔
      ∃ s o, v.prepareCall tx p c = .ok s ∧ s.run = .ok o ∧ o.error = none ∧ o.output = out := by
  rw [ethCall_eq]
  rcases v.prepareCall tx p c with e | s <;> simp [bind, Except.bind]
  rcases s.run with e | o <;> simp [Except.mapError, callAnswer]
  split <;> simp_all

/-- A call answers the revert error with data `d` exactly when its message reverts.

The output of the revert is then `d`. -/
theorem ethCall_eq_revertError_iff {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} {d : ByteArray} :
    v.ethCall tx p c = .error (revertError d) ↔
      ∃ s o, v.prepareCall tx p c = .ok s ∧ s.run = .ok o ∧ o.error = some .revert ∧
        o.output = d := by
  rw [ethCall_eq]
  rcases hp : v.prepareCall tx p c with e | s
  · simp only [bind, Except.bind, Except.error.injEq, reduceCtorEq, false_and, exists_false,
      iff_false]
    rintro rfl
    exact (prepareCall_error hp).1 rfl
  · simp only [bind, Except.bind, Except.ok.injEq, exists_and_left, exists_eq_left']
    rcases s.run with e | o
    · simp only [Except.mapError, reduceCtorEq, false_and, exists_false, iff_false]
      intro h
      have := congrArg RpcError.code (Except.error.inj h)
      simp [callInternalError, revertError, internalError, executionReverted,
        ErrorCode.toRpcError] at this
    · simp only [Except.mapError, Except.ok.injEq, exists_eq_left', callAnswer]
      split
      · simp_all
      · simp_all only [Except.error.injEq, true_and]
        exact ⟨revertError_inj, congrArg _⟩
      · rename_i e hne heq
        simp only [Except.error.injEq]
        exact ⟨fun h => absurd (congrArg RpcError.code h) (haltError_code _).1,
          fun h => (hne (Option.some.inj (heq.symm.trans h.1))).elim⟩

/-- The message of a call on the block `r` runs on the state after `r`.

It starts at depth 0, from the sender to the recipient, with the value of the request.

A call to a recipient carries the input of the request as its data. -/
theorem prepareCall_message {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} {r : BlockRecord} {s : CallSetup} (hr : v.resolve p = .ok (some r))
    (h : v.prepareCall tx p c = .ok s) :
    s.state.parent = ⟨r.state, ∅, ∅, ∅, ∅⟩ ∧ s.sender = tx.sender.getD c.sender ∧
      s.message.caller = s.sender ∧ s.message.target = tx.to ∧ s.message.depth = 0 ∧
      s.message.value.toNat = tx.value.getD 0 ∧
      (tx.to.isSome → s.message.data = tx.input.getD .empty) := by
  obtain ⟨r', hr', hparent, hsender, hcaller, htarget, hdepth, hvalue, hdata, -⟩ :=
    prepareCall_ok h
  obtain rfl : r' = r := Option.some.inj (Except.ok.inj (hr'.symm.trans hr))
  exact ⟨hparent, hsender, hcaller, htarget, hdepth, hvalue, hdata⟩

/-- A call that names no fee takes no wei from its sender before its message runs. -/
theorem prepareCall_balance_of_namesFee_false {v : ChainView} {tx : GenericTransaction}
    {p : BlockParam} {c : CallChoices} {r : BlockRecord} {s : CallSetup}
    (hfee : tx.namesFee = false) (hr : v.resolve p = .ok (some r))
    (h : v.prepareCall tx p c = .ok s) :
    (s.state.getAccount s.sender).balance = (r.account s.sender).balance := by
  obtain ⟨r', hr', h⟩ := ofBlock_eq_ok.mp h
  obtain rfl : r' = r := Option.some.inj (Except.ok.inj (hr'.symm.trans hr))
  simp only [bind, Except.bind] at h
  repeat' (split at h)
  all_goals simp only [pure, Except.pure, reduceCtorEq, Except.ok.injEq] at h
  all_goals subst h
  all_goals exact ((bought_ok (by assumption)).2 hfee).trans (congrArg _ getAccount_ofBlock)

/-- A call that names no fee never fails for the balance of a sender that holds its value.

The balance is read after the block `r`. -/
theorem ethCall_ne_insufficientFunds {v : ChainView} {tx : GenericTransaction} {p : BlockParam}
    {c : CallChoices} {r : BlockRecord} {e : RpcError} (hfee : tx.namesFee = false)
    (hr : v.resolve p = .ok (some r))
    (hvalue : tx.value.getD 0 ≤ (r.account (tx.sender.getD c.sender)).balance.toNat) :
    v.ethCall tx p c = .error e → e.code ≠ insufficientFunds.code := by
  rw [ethCall_eq]
  rcases hp : v.prepareCall tx p c with e' | s
  · simp only [bind, Except.bind, Except.error.injEq]
    rintro rfl hcode
    obtain ⟨r', hr', hlt⟩ := (prepareCall_error hp).2 hfee hcode
    obtain rfl : r' = r := Option.some.inj (Except.ok.inj (hr'.symm.trans hr))
    omega
  · simp only [bind, Except.bind]
    rcases s.run with e' | o
    · simp only [Except.mapError, Except.error.injEq]
      rintro rfl
      simp [callInternalError, internalError, insufficientFunds, ErrorCode.toRpcError]
    · simp only [Except.mapError, callAnswer]
      split
      · simp
      · simp only [Except.error.injEq]
        rintro rfl
        simp [revertError, executionReverted, insufficientFunds]
      · simp only [Except.error.injEq]
        rintro rfl
        exact (haltError_code _).2

/-- A call whose sender holds less than its value, after the block `r`, answers no data. -/
theorem ethCall_ne_ok_of_balance_lt_value {v : ChainView} {tx : GenericTransaction}
    {p : BlockParam} {c : CallChoices} {r : BlockRecord} {out : ByteArray}
    (hr : v.resolve p = .ok (some r))
    (hbalance : (r.account (tx.sender.getD c.sender)).balance.toNat < tx.value.getD 0) :
    v.ethCall tx p c ≠ .ok out := by
  intro h
  obtain ⟨s, -, hs, -⟩ := ethCall_eq_ok_iff.mp h
  obtain ⟨r', hr', -, -, -, -, -, -, -, hle⟩ := prepareCall_ok hs
  obtain rfl : r' = r := Option.some.inj (Except.ok.inj (hr'.symm.trans hr))
  omega

end ChainView

end EthLib.Execution.Rpc
