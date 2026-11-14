# Changelog

This file lists the changes of each release that a caller of EthLib may need to act on.
The version is the same in `pyproject.toml` and `lakefile.lean`.

## 0.4.0

Not yet released.

### Changes that break callers

- In Lean, the proof modules `FastConfirmationCommittees`, `FastConfirmationConfirmedRoot`, `FastConfirmationIndicators`, `FastConfirmationSets` and `FastConfirmationSupporters` move under `EthLib.Consensus.Proofs.ForkChoice.FastConfirmation` as `Committees`, `ConfirmedRoot`, `Indicators`, `Sets` and `Supporters` ([#2566](https://github.com/ethereum/EthLib/pull/2566)).
  The declarations of the former `FastConfirmation` module move to `FastConfirmation.Basic`, and importing `FastConfirmation` still provides them and all five leaves.
  Declaration namespaces and statements are unchanged.

- `ssz.get_generalized_index` names a field of a container only by its name ([#2480](https://github.com/ethereum/EthLib/issues/2480)).
  A position given for a field is refused with the error for an unknown field.
  In addition, a path takes `__active_fields__` and `__selector__`, the mixed-in nodes of a progressive container and of a union.

- In Python, `consensus.api_post` and `consensus.api_gossip_event` return the data of each event as its JSON text, instead of the parsed value ([#2515](https://github.com/ethereum/EthLib/pull/2515)).
  This is the `data` field of the Beacon API event stream, and the form that the fork choice events already return.
  A caller that needs the value applies `json.loads` to that text.

- In Lean, the SSZ exports read a Python value directly, without writing it as JSON first ([#2475](https://github.com/ethereum/EthLib/issues/2475)).
  In Lean, `valueOfJson` becomes `valueOf`, `jsonOfValue` and `jsonOfValues` become `pyOfValue` and `pyOfValues`, and `descOf`, `tagged`, `optionalNat`, `pair` and `readValue` take a `PyValue`.
  Bytes given as `bytes` are taken as they are, instead of being written as hex and read back.
  Nothing breaks in Python: every input gives the same result or the same error as before.

- In Lean, the shuffle, custody, keystore and discv5 callers of SHA-256 keep the digest as a `Vector UInt8 32` ([#2189](https://github.com/ethereum/EthLib/issues/2189)).
  `Shuffle.bucketBits` and `Keystore.passwordChecksum` return one, and `Shuffle.bitAt` and `DataAvailability.firstUInt64` take one.
  A caller that needs the bytes applies `packBytes`, and `Sha256.packBytes_hash32` gives back the byte-array digest.
  The keystore checksum theorems compare the checksum with `store.checksum` directly, and `checksumVector` is removed: use `passwordChecksum`.
  Nothing breaks in Python.

- The execution RPC answers `eth_simulateV1` with its simulated blocks ([#2108](https://github.com/ethereum/EthLib/issues/2108)).
  The results of the calls are not yet in the blocks.
  In Lean, `fillHeader`, `outputChecks_fillHeader` and `runBody_fillHeader` move from `EthLib.Engine` to `EthLib.Execution.Blocks`, and `SimulateChoices` gains `gasCap`.
  Nothing breaks in Python.

- In Lean, the block environment gains the field `blobGasPrice` ([#2108](https://github.com/ethereum/EthLib/issues/2108)).
  A simulation sets the base fee per blob gas with it, and its default `none` keeps the price of the excess blob gas.
  Supply that field in positional constructors, or use structure notation with its default.
  The checks and the run of a transaction, and the simulation overrides of a body, take optional lifted rules.
  A simulation can skip the nonce check and lift the gas caps of EIP-8037 with them.
  The sender check gains a flag for the nonce check.
  Nothing breaks in Python.

- In Lean, the transaction environment gains the field `precompiles` ([#2108](https://github.com/ethereum/EthLib/issues/2108)).
  It gives the address of the precompile that a call to each address runs.
  Its default `some` keeps each precompile at its own address, so a real block is unchanged.
  Supply that field in positional constructors, or use structure notation with its default.
  The checks of a transaction, its run and the body of a block take optional simulation overrides.
  A simulation can give the sender in place of the signature, and that sender may have code.
  The sender check gains a flag for that case.
  Nothing breaks in Python.

- The execution RPC checks the requests of `eth_simulateV1` before their blocks run ([#2107](https://github.com/ethereum/EthLib/issues/2107)).
  In Lean, `call_unknown` requires the method name to differ from `eth_simulateV1`.
  Nothing breaks in Python: `rpc.apply_overrides` gives the state root after the account overrides of one block.

- The execution RPC serves `eth_getBlockAccessList` and `debug_getRawBlockAccessList` ([#2106](https://github.com/ethereum/EthLib/issues/2106)).
  In Lean, `BlockRecord` gains the optional field `accessList` for the retained list.
  Supply that field in positional constructors, or use structure notation with its `none` default.
  `Follows` requires each retained list to equal the execution builder's list.
  `call_unknown` requires the method name to differ from both access-list method names.
  Nothing breaks in Python: `rpc.serve` takes the new optional argument `pruned_access_lists` for block numbers whose lists are unavailable.
  `rpc.encode_block_access_list` encodes a JSON list as its EIP-7928 RLP bytes.

- In Lean, `Frame` gains the field `slashed`, after `pubkeysDistinct` ([#1451](https://github.com/ethereum/EthLib/issues/1451)).
  A validator slashed before a step, at a registry position, is slashed after it at the same position.
  A proof that builds a `Frame` with an anonymous constructor adds that field.
  `frame_setValidatorAt_of_whole`, `frame_setValidator_of_whole` and `frame_setValidator` take a new premise `old.slashed = true → validator.slashed = true` after the proof of the key.
  A caller passes `id` when the new validator copies the flag of the old one, and `fun _ => rfl` when it is slashed.
  `initiateValidatorExit_balances_eq_and_pendingConsolidations_eq` moves to `Consensus/Proofs/Transition/PendingConsolidations.lean`, which `BalanceDrift.lean` imports publicly.

- In Lean, the results on slashed flags state them at each position of the registry, through `slashedFlagAt state position`, the read `(state.validators.data[position]?).map (·.slashed)` ([#2187](https://github.com/ethereum/EthLib/issues/2187)).
  From Gloas the registry has no limit in its type, so a position may lie beyond every `ValidatorIndex`.
  A proof whose goal spells out the read unfolds the name first, as in `simp only [slashedFlagAt] at h`.
  `slashedFlag_initiateValidatorExit` is renamed `slashedFlagAt_initiateValidatorExit`, and it takes a `position : Nat` in place of an index.
  The second conjunct of `slashValidator_slashedFlag` holds at each position other than `slashedIndex.toNat`.
  A caller that read either at an index `i` reads it at `i.toNat`.
  The new `slashedFlag_eq_of_slashed` turns equal flags there into equal values of `slashedFlag` at `i`.
  `slashIfSlashable_ok` and `foldlM_slashIfSlashable` gain a last conjunct: no slashed flag changes at a position other than that of their index, or that none of their indices names.
  A pattern that takes them apart needs a fourth component.
  `UpgradeFrame` gains the field `slashed`, since each upgrade keeps every slashed flag.
  `ElectraKept` gains the same conjunct, so a pattern that takes it apart needs a fourth component too.
  `UpgradeFrame.trans_blockFrame` takes the new premise `slashed`: the steps after the upgrade keep every slashed flag.
  A block frame alone may slash, so it cannot give the field.
  Compose the block frames of the steps first, and pass their slashed flags once.
  `slashedFlagAt_processProposerSlashing` and `slashedFlagAt_processAttesterSlashing` state that a slashing changes flags only at the positions that it names.
  `slashedFlagAt_foldlM` states the same for a fold of such steps.
  `slashed_setValidatorAt` is renamed `slashedFlagAt_setValidatorAt`.
  `foldlM_ok_invariant_of_mem` moves to `Base/Proofs/MapM.lean`, in the namespace `EthLib.Base`.

- `engine_forkchoiceUpdated` checks that the most recent block of proof of work on the chain of the head is terminal, as step 3 of the method and step 2 of payload validation of Paris require.
  A head whose chain fails the check is `INVALID`, with the zero hash, and the head does not change.
  Once the known finalized block is a payload of the tree, a zero safe or finalized hash gives `-38002`.
  The latest valid hash of an invalid head is zero when its latest valid block is of proof of work.
  In Lean, `KnownPayload` has the new field `powTotalDifficulty`, `none` for a payload, so its anonymous constructor takes a fifth value.
  `forkchoiceUpdated` takes a `TransitionConfiguration` first, and `forkchoiceUpdatedCall` takes one after the chain configuration.
  `forkchoiceUpdated_valid`, `forkchoiceUpdated_of_belowFinalized`, `forkchoiceUpdated_valid_none_iff`, `forkchoiceUpdated_of_invalid`, `forkchoiceUpdated_of_onChain` and `forkchoiceUpdated_eq_error_iff` state the terminal block check.
  `forkchoiceUpdated_valid`, `forkchoiceUpdated_of_onChain` and `forkchoiceUpdated_eq_error_iff` also state the rule on zero hashes, and `forkchoiceUpdated_of_invalid` answers `latestValidHash` in place of `latestValid`.
  In Python, a block of the tree of `engine.forkchoice_updated` may carry `totalDifficulty` and `parentTotalDifficulty`.
  The function takes the required keyword-only argument `terminal_total_difficulty`, as `engine.new_payload_on_chain` does.
  A tree with no block of proof of work passes the check whatever that value, which must be below `2^256`.
  The native `engine_forkchoice_updated` takes that value after the finalized block.
- `engine_newPayload` on a chain checks that a parent of proof of work is a terminal block, as step 2 of payload validation of Paris requires.
  A parent that fails the check makes the payload `INVALID`, with the zero hash and the new reason code 407.
  In Lean, `PayloadError` has the new constructor `invalidTerminalBlock`, with that code.
  `newPayloadOnChain` takes two new arguments before the chain: a `TransitionConfiguration`, and the total difficulty of the last block of the chain.
  Its theorems take both values, and `newPayloadOnChain_of_stateTransition_ok`, `newPayloadOnChain_of_stateTransition_error` and `newPayloadOnChain_of_buildPayload` take the hypothesis that the parent passes the check.
  In Python, `engine.new_payload_on_chain` takes the required keyword-only arguments `terminal_total_difficulty` and `total_difficulty`, and the native `engine_new_payload_on_chain` takes them after the recent blocks.
  A last block from Paris on passes the check, so then any total difficulty, and any terminal total difficulty below `2^256`, do.
- In Lean, the bound on the extra data of an Engine payload is the named constant `Execution.Blocks.MAX_EXTRA_DATA_BYTES`, in place of the literal `32`.
  The statements of `anyPayload_executionPayloadJson`, `payloadV4_executionPayloadV4Json`, `payloadOfBlock_extraData` and `newPayloadParams_json` change only by that name, and so do `payloadOfBlock` and `anyPayload`.
  The constant is `32`, so a proof that used `omega` on the bound first unfolds it, as in `simp only [MAX_EXTRA_DATA_BYTES]; omega`.
- In Lean, `EpochFrameLaws` now extends `EpochStepLaws`, which holds every law except those for a new validator and for the queue of pending deposits.
  The theorems that need neither law moved from the `EpochFrameLaws` namespace to the `EpochStepLaws` namespace, with the same statements, and they now take the smaller structure.
  Dot notation on a value of either structure still finds them; a full name such as `EpochFrameLaws.processSyncAggregate` becomes `EpochStepLaws.processSyncAggregate`.
- In Lean, `processEpoch_split_of_lt_altair` moved from the `EpochFrameLaws` namespace to the `EpochStepLaws` namespace, with the same statement, and it now takes the smaller structure.
  Dot notation on an `EpochFrameLaws` value still finds it.
  A call by the full name `EpochFrameLaws.processEpoch_split_of_lt_altair laws` becomes `EpochStepLaws.processEpoch_split_of_lt_altair laws.toEpochStepLaws`.
- In Lean, the JSON readers and writers of the base types moved from `EthLib.Engine.Json` to `EthLib.Serialization.JsonRpc`, with their theorems.
  They are `hexValue`, `hexDigits`, `bytesOf`, `bytes`, `fixed`, `address`, `quantity`, `bytesMax`, `uint64`, `paramsArray`, `array`, `fields`, `hasExactly`, `field`, `dataJson`, `quantityJson`, `listJson` and `optionJson`.
  Their namespace is now `EthLib.Serialization.JsonRpc`.
  The readers among them return `Read`, an alias of `Except String`, in place of `Except EngineError`, and reject an input with a reason.
  An Engine decoding lifts that reason to `EngineError.invalidParams`, through `Engine.Json.lift` and its `MonadLift` instance, so every Engine decoder returns what it returned before.
  `withdrawal` and `withdrawalJson`, with their theorems, moved to `EthLib.Execution.Rpc`.
  The Python bindings are unchanged.

- In Lean, `DirectSafety.EnoughStake run high` requires the stake floor only at epoch calls whose current epoch is at most `high + 1`.
  The floor reaches one epoch past the finalized epoch of `b` in `accountable_safety`, and one epoch past `j.epoch` in the other three direct safety endpoints.
  Move `j` (and `k` for `accountable_justified_unique`) before the stake premises.
  An existing unbounded floor proof adapts as `fun call _ => oldEnough call`.
  Pass a target-epoch bound as the new `within` argument of `quorum_count`.
  Remove the `starts` argument from `accountable_safety` and `accountable_safety_justified`, but keep it for `accountable_justified_unique`.
  `conflict` and `ordered` imply the removed bound on the slot of `x`, so the theorems cover the same runs as before.
  The drift horizon in the conclusion of `accountable_safety` is the finalized epoch of `b`, not the larger of the two finalized epochs; `ordered` makes them equal.

- In Lean, the direct safety endpoints bound the unslashed active stake at `x`, `unslashedKeys x.state`, in place of `activeKeys x.state` ([#2187](https://github.com/ethereum/EthLib/issues/2187)).
  `Accountable` takes the shared prefix and the two tails, `shared left right`, in place of the two full runs, and `accountableKeys` takes them in place of the two full runs and the reference state.
  Slashing evidence counts only in the tails; double votes still count over the full runs, and proposer slashings in the tails still count.
  `accountableKeys` keeps only the unslashed keys active at `x`.
  `recentKeys` keeps only unslashed keys, `referenceLoss` sums over `unslashedKeys x`, and `referenceGain` subtracts the support of `unslashedKeys x`.
  So `boundaryStake`, and through it `stateDrift` and `derivedDrift`, count only unslashed recent stake.
  `Run.slashed_evidence` holds for a run from any state, with no `genesis` argument, and concludes `SlashedAt x.state v.pubkey ∨ run.SlashingEvidence v.pubkey`.
  `SlashedAt` names the predicate that `referenceLoss` stated inline before.
  `verifiedConflict_of_accountable` takes `shared left right` and concludes `VerifiedConflict (shared.append left) (shared.append right) key`.
  Pass `shared left right` where a caller passed `shared.append left`, `shared.append right` and `x`.
  `DirectSafety.accountable_safety_justified_terminal` and `Store.Reachable.finalized_ancestor_or_accountable` change the same way: their stake alternative bounds the unslashed active stake, at `x` or at the anchor state, by `accountableKeys` of the shared prefix and the two tails.
  The new Lean declarations are `DirectSafety.SlashedAt`, `DirectSafety.unslashedKeys`, `DirectSafety.EpochCall.pubkeysDistinct` and `Run.pubkeysDistinct`.
  `Run.pubkeysDistinct` gives distinct keys at the end of a run from genesis; `EpochCall.pubkeysDistinct`, `view_quorum_count` and `view_voters_recent` read it.

- In Lean, `DirectSafety.HashEvidence objects` is stated through the searches `findMessageCollision` and the new `findZeroRoot`, in place of a bounded existential ([#2187](https://github.com/ethereum/EthLib/issues/2187)).
  No C export or Python function changes, and every theorem that mentions `HashEvidence` keeps its statement.
  `hashEvidence_iff` proves that the new body is equivalent to the old one, for every list of objects and with no hypothesis.
  `findZeroRoot_valid` and `findZeroRoot_eq_none_iff` say what the new search returns and when it fails.
  The two bodies are not definitionally equal.
  A proof that unfolds `HashEvidence` to take it apart first rewrites with `hashEvidence_iff`, or applies `hashEvidence_iff.mp`.
  A proof that builds the evidence as an `Or` of the old form applies `hashEvidence_iff.mpr`.

- In Lean, the four rules by which one justification step finalizes a checkpoint have one definition, `FinalizationStepRule state after checkpoint` ([#2187](https://github.com/ethereum/EthLib/issues/2187)).
  The bits come from the state after the step, the epoch and the justified checkpoints from the state before it.
  `weighJustificationAndFinalization_finalized` states its second disjunct as `FinalizationStepRule state after after.finalizedCheckpoint`, with the same unfolded body.
  `DirectSafety.FinalizationRule call checkpoint` is `FinalizationStepRule call.cached call.weighed checkpoint`, with the same unfolded body.
  A proof that took either apart by name first unfolds `FinalizationStepRule`.
  No C export or Python function changes.

- `verify_kzg_proof` checks its inputs in the order of EIP-4844: the commitment, `z`, `y`, then the proof.
  When more than one input is invalid, the first in that order gives the error.
  Before, it checked the proof second, so an input with an invalid `z` and an invalid proof raised the error of the proof.
  It now raises the error of `z`.
  The verdicts are unchanged, and so are the errors of an input with at most one invalid argument.

- In Lean, `verifyBlobKzgProof_binding` states its hypotheses as EIP-4844 converts the commitment and the proof.
  It takes the raw bytes, the values that `bytesToKzgCommitment` and `bytesToKzgProof` return, and the points that `uncompressG1` decodes from them.
  A caller that holds `validateKzgG1Point b = .ok C` gets the two new hypotheses from `bytesToKzgCommitment_of_validateKzgG1Point` and `uncompressG1_of_validateKzgG1Point`.
  The same holds for the proof, with `bytesToKzgProof_of_validateKzgG1Point`.
  The C exports and the Python functions are unchanged.

- Along a chain from genesis, the public keys of the validators stay a prefix and stay distinct ([#1421](https://github.com/ethereum/EthLib/issues/1421)).
  No C export or Python function changes.
  In Lean, `Frame` and `UpgradeFrame` gain the fields `pubkeysPrefix` and `pubkeysDistinct`.
  They bring back the key-keeping fact that [#1950](https://github.com/ethereum/EthLib/pull/1950) removed for [#1908](https://github.com/ethereum/EthLib/issues/1908), where it was named `KeysKept`.
  `validatorKeys` lists the keys of the registry and `PubkeysDistinct` says that they have no repeat.
  `validatorKeys_prefix_and_distinct_of_chainSteps` states, for a run of steps, that the keys of its first state are a prefix of the keys of its last state.
  It also states that distinct keys stay distinct.
  `validatorKeys_prefix_and_distinct_of_genesis_chainSteps` states both along a chain from genesis.
  `frame_addValidatorToRegistry` takes a proof that the key is not in the registry, and `EpochFrameLaws.addValidatorToRegistry` takes it too.
  `frame_setValidatorAt_of_whole`, `frame_setValidator_of_whole`, `EpochFrameLaws.setValidator` and the `setValidatorAt` field of `EpochFrameLaws` take the old validator and a proof that the state holds it at that position.
  They also take a proof that the new validator keeps the key of the old one.
  `frame_setValidator`, `EpochFrameLaws.setValidator_of_sameBalance` and `EpochFrameLaws.setValidatorAt_of_sameBalance` take the proof of the key.
  `applyPendingDeposit_cases` decomposes a pending deposit.
  `addValidatorToRegistry_slot` states that adding a validator keeps the slot.

- In Lean, the gossip message ID has its length in its type.
  `Gossip.messageId` returns `Vector UInt8 20` in place of a `ByteArray`.
  A caller that needs a `ByteArray` takes `Base.packBytes (messageId fork topic data)`.
  `messageId_size` is removed, since the type states the length.
  `messageId_of_ok` and `messageId_of_error` state the ID as `(Sha256.hash32 input).take 20`.
  The new `packBytes_messageId_of_ok` and `packBytes_messageId_of_error` state their former equations, through `Base.packBytes`.
  The C export `eth_gossip_message_id` and the Python `gossip.message_id` are unchanged.

- Slashing-protection imports use EIP-3076's minimal strategy ([#1963](https://github.com/ethereum/EthLib/issues/1963)).
  Import compacts both the held record and the file: each key keeps its greatest block slot and its greatest source and target epochs, taken independently, without signing roots.
  So a repeat of any message held before the import is refused, and so is a block at or before the slot limit, or a vote with a source before the source limit or a target at or before the target limit.
  The keys of the record come out in byte order.
  The JSON format and the C and Python signatures are unchanged.

- A checkpoint of a fork-choice store comes from the anchor, a held state or its pull-up ([#1423](https://github.com/ethereum/EthLib/issues/1423)).
  No C export or Python function changes.
  In Lean, `Store.Reachable.justified_origins` and `Store.Reachable.finalized_origins` state this for a reachable store.
  In the new module `Consensus.Proofs.ForkChoice.CheckpointAncestry`, `Store.Reachable.finalized_ancestor_or_accountable` gives three cases for the finalized checkpoint of the store.
  It is at or before the anchor epoch, or it is on the chain of the justified checkpoint at the first slot of its epoch.
  Otherwise two runs from the anchor to held states of the store bound the accountable stake, or show hash evidence.
  It asks that every block was imported with the setting of the signature checks of the run from genesis, as `Store.BlockStatesFromParents`, which `Store.ForwardReachableWith.blockStatesFromParents` gives.
  The drift of its bound counts from the anchor, so the bound loosens as the justified epoch moves away from the anchor epoch.
  `DirectSafety.TerminalView` reads the checkpoints of the last state of a run, or of one justification step on it, as fork choice runs it.
  `DirectSafety.accountable_safety_justified_terminal` states direct accountable safety for two such views, and like the theorems it extends it asks no bound on the fork of either run.
  `DirectSafety.accountable_safety_justified` is its case without a step, and its statement is unchanged.
  The other new Lean declarations are `TerminalView.state`, `TerminalView.enough`, `TerminalQuorum`, `TerminalQuorum.source`, `TerminalQuorum.voters`, `TerminalQuorum.currentEpoch_le`, `ViewQuorum`, `ViewQuorum.source`, `ViewQuorum.target`, `ViewQuorum.voters`, `ViewQuorum.state`, `ViewQuorum.eq_inl_of_realized`, `view_field_crossing`, `view_finalized_quorums`, `view_quorum_attestations`, `view_quorum_count`, `view_quorum_target_binding`, `view_conflicting_fields_quorums`, `view_voters_recent`, `checkpoint_binding_prefixes` and `hashObjects_append_subset`, all in `DirectSafety`, and `Store.ancestorRoots_of_parent`, `Store.updateCheckpoints_unrealizedJustifications` and `Store.updateUnrealizedCheckpoints_unrealizedJustifications`.
  The new `Store.SameCheckpoints` says that two stores have the same justified, finalized, unrealized justified and unrealized finalized checkpoints.
  `Store.SameCheckpoints.refl`, `.justified`, `.finalized`, `.unrealizedJustified` and `.unrealizedFinalized` read it; a caller that names these projections does not depend on the order of the four checkpoints.
  `Store.storeTargetCheckpointState_frame`, `Store.onAttestation_frame`, `Store.onAttesterSlashing_frame`, `Store.recordBlockTimeliness_frame` and `Store.updateProposerBoostRoot_frame` end with two new conjuncts.
  They state `Store.SameCheckpoints` of the store and the result, and that the unrealized justifications are unchanged.
  `Store.onTickPerSlot_frame` ends with a new conjunct: a store `moved`, the store itself or `updateCheckpoints` with its unrealized checkpoints, has `Store.SameCheckpoints` with the result, and the unrealized justifications are unchanged.
  `Store.computePulledUpTip_frame` ends with a new conjunct: the held state of the tip and the result of its justification and finalization.
  The conjunct also gives a store `moved` with `Store.SameCheckpoints` of the result, built from that result, and the unrealized justifications with that result's current justified checkpoint added for the tip.
  A pattern that destructures the four checkpoints destructures them in one nested pattern.
  A caller that destructures one of these seven results adds one pattern, and only if its last pattern named the old last conjunct.
  A pattern that ends in `-` needs no change.
  A projection of the old last conjunct gains `.1`.
  So `.2.2` of `Store.onAttestation_frame` and `Store.onAttesterSlashing_frame` becomes `.2.2.1`, and `.2.2.2.2` of `Store.onTickPerSlot_frame` becomes `.2.2.2.2.1`.
  The `.2.2.2` of the other four frames becomes `.2.2.2.1`.
  The new `Store.catchUp_preserves` states that catch-up keeps each property of the store that every tick within a slot keeps.
  It has the form of `Store.onBlockWithVotes_preserves`.
  `Store.catchUp_frame`, `Store.catchUp_ordered` and the catch-up step of `Store.onTick_checkpointStates_latestMessages` now read it, with unchanged statements.
  The new `Store.onTick_ok` splits a tick into the slot of its time, the catch-up to that slot and one tick within it.
  `Store.onTick_frame`, `Store.getCurrentSlot_onTick`, `Store.onTick_ordered`, `Store.onTick_checkpointStates_latestMessages` and `Store.exists_getCurrentSlot_onTick_ge` now read it, with unchanged statements.
  The new `Store.Reachable.linked_of_unknown` gives the links of a reachable store whose anchor parent is unknown, and `Store.Reachable.parentsBelow` keeps its statement.

- The theorem that a block leaves its header as the latest block header holds at every fork ([#2061](https://github.com/ethereum/EthLib/issues/2061)).
  In Lean, `latestBlockHeader_processBlock` drops its `gloas` argument, and its conclusion is unchanged.
  Callers remove that argument.

- The cumulative churn bounds also hold for idle queues ([#1451](https://github.com/ethereum/EthLib/issues/1451)).
  In Lean, `churnQueue_foldlM_le` drops its `first` argument, and `computeExitEpochAndUpdateChurn_foldlM_le` and `computeConsolidationEpochAndUpdateChurn_foldlM_le` drop their `open_` argument.
  Callers remove that argument.
  The exact `_spend` equalities keep it.
- A req/resp payload now fails when bytes follow the chunk that completes its declared length.
  A reader must reject any bytes that remain after it has read the declared number of SSZ bytes.
  The decoder read the whole Snappy stream.
  So it accepted chunks after the one that completes the length, if they add no bytes: padding, reserved skippable chunks, a second stream identifier or an empty data chunk.
  With a declared length of 0, the reader now reads the stream identifier alone, so any chunk after it fails too.
  `reqresp.decode_payload` and `reqresp.decode_response_chunk` raise `ReqRespError` with the message "N bytes follow the last chunk of the payload", and the C exports return the new error code 10.
  In Lean, `decodePayload` reads the stream with the new `Snappy.readFrames`, which stops at the chunk that completes the declared length and returns the bytes after it.
  `Snappy.readChunks` is its chunk loop, and the new module `Networking.Proofs.Snappy.Read` proves their properties.
  `ReqRespError` gains the constructor `trailingBytes`.
  The last conjunct of `decodePayload_ok` and `decodePayload_eq_ok_iff` is now `Snappy.readFrames … = .ok (d.data.toList, [])` in place of `Snappy.decodeFrames … = .ok d`.
  `decodeFramesList_of_readFrames` gives the list form of the old conjunct, and the new `decodePayload_append_ne_ok` proves that bytes appended to a payload that decodes make it fail.
- The leanXMSS signing lemmas over a map of monads now derive, from the monad laws, that the map keeps `map` ([#1385](https://github.com/ethereum/EthLib/issues/1385#issuecomment-6722640861)).
  `findCodeword_map_monad`, `otsSign_map_monad`, `signLayer_map_monad` and `signDerived_map_monad` require `LawfulMonad` instances for both monads instead of an explicit `map_map` argument.
  Drop that argument at each call.
  `Sphincs.Unforgeability.map_monad_map` moves to `HashSig.map_monad_map`, so leanXMSS and leanSPHINCS share one proof that such a map keeps `map`.
- From Gloas, the discount for empty slots of the fast confirmation rule also counts the votes for the pending node of the parent ([#1368](https://github.com/ethereum/EthLib/issues/1368), [#1458](https://github.com/ethereum/EthLib/issues/1458)).
  A parent has three nodes from Gloas: a pending one, and a full and an empty one for the two answers on its payload.
  The discount counted only the votes for the full or the empty node that the block builds on.
  It counts the votes for that node and for the pending node, and the votes for the other of the two stay out.
  A vote cast in the slot of the block it names supports the pending node of that block.
  A member of the committees of the empty slots can hold such a vote for the parent, and the discount missed it.
  Before Gloas the parent has only its pending node, and the discount keeps its value.
  No signature of a C export or Python function changes.
  From Gloas the threshold can be lower, so a `fast_confirmation` step of `fork_choice` can confirm a block sooner.
  In Lean, `Store.getNodeSupportBetweenSlots` takes a list of nodes in place of a node, and counts a vote for any of them.
  `getNodeSupportBetweenSlots_le` takes that list too.
- The block supply bound and the Glamsterdam equality now follow from the exact block supply equation ([#1902](https://github.com/ethereum/EthLib/issues/1902)).
  No C export or Python function changes.
  In Lean, `supply_systemCall`, `supply_systemCall_join`, `supply_startSystemCalls`, `supply_blockRequests` and `applyTransactions_supply` are gone from `EthLib.Execution.Proofs.Blocks.Supply`.
  The new `SystemCallBurns.total_eq_zero_of_glamsterdam`, `StartSystemCallsBurns.total_eq_zero_of_glamsterdam`, `TransactionsBurns.total_eq_zero_of_glamsterdam`, `RequestsBurns.total_eq_zero_of_glamsterdam`, `BlockRequestsBurns.total_eq_zero_of_glamsterdam` and `BodyBurns.total_eq_zero_of_glamsterdam` in `EthLib.Execution.Proofs.Blocks.Burn` prove that the certified losses are 0 from Glamsterdam.
  `withdrawnWei`, `rewardWei`, `createdWei`, `burnedWei` and the supply lemmas of the DAO transfer, the withdrawals and the rewards move to `EthLib.Execution.Proofs.Blocks.Burn`, with the same names.
  `EthLib.Execution.Proofs.Blocks.Burn` no longer imports `EthLib.Execution.Proofs.Blocks.Supply`, so import the latter for `headerBurnedWei`, the `applyBody_supply` theorems and the `stateTransition_supply` bounds.
- From Gloas, the rewards and penalties and the inactivity updates of an epoch now fail where a registry position of 2^64 or more would become a validator index ([#1883](https://github.com/ethereum/EthLib/issues/1883)).
  The specification builds a `ValidatorIndex` for each position when it applies the deltas, and for each eligible validator when it lists the eligible indices.
  EthLib took such a position modulo 2^64, so it credited the balance, or updated the inactivity score, of another validator.
  Before Gloas the registry stays within its limit, which is below 2^64, so nothing changes there.
  No C export or Python function changes.
  In Lean, `applyDeltas_eq_ok_iff` now reads the balance at the position itself, not at the position modulo 2^64, and adds the condition that the position is below 2^64.
  `applyAllDeltas_balances`, `foldlM_applyAllDeltas_balances` and `processRewardsAndPenalties_balances_of_altair` no longer take a bound on the size of the registry.
- The FFG chain theorems now derive that the block of each justified checkpoint is in the chain of the block of its recent epoch from the order of the roots at consecutive slots, instead of assuming it ([#1420](https://github.com/ethereum/EthLib/issues/1420)).
  No C export or Python function changes.
  In Lean, the field `chain` of `SlackStepBounds` becomes `links`, which asks the map from roots to blocks to keep in order the roots of consecutive slots (`rootLinks`).
  `SlackChainInvariant` gains the field `roots`, a `RootsAbove` fact that the new `FfgRoots.lean` keeps along each chain step.
  The new `ChainRoot` orders the roots by the links of the states that genesis reaches, and `slackJustifiedCheckpoints_chainRoot_of_chainSteps` uses it, so it asks no order hypothesis.
  The new `recentJustified` names the justified checkpoint of a recent epoch, and `RootsAbove.le_of_getBlockRoot` gives the order that justification reads; `RootsAbove.of_chainStep`, `RootsAbove.of_initializeBeaconStateFromEth1` and `toChainRoot` are new too.
  New shared lemmas: `getBlockRootAtSlot_ok_iff`, `getBlockRootAtSlot_exists`, `getBlockRootAtSlot_between` and `getBlockRootAtSlot_congr` (`Accessors.lean`), `advanceSlot_previousJustified`, `processBlock_blockRoots`, `processUpgrades_slot` and `processUpgrades_blockRoots`.
- From Gloas, the pending deposits of an epoch now fail at every deposit they read to a key whose first validator sits at a registry position of 2^64 or more ([#1883](https://github.com/ethereum/EthLib/issues/1883)).
  The specification builds a `ValidatorIndex` from that position before it tests the validator, so it fails there.
  EthLib failed only when it credited such a deposit, and missed the deposit to a validator that exits and is not withdrawn, and the deposit beyond the churn.
  Before Gloas the registry stays within its limit, which is below 2^64, so nothing changes there.
  No C export or Python function changes.
  In Lean, `depositTargetStatus` now returns an `Except AccessorError (Bool × Bool)`.
  The fields `stops`, `used`, `appliedFilter` and `movedFilter` of `PassPendingDepositsFacts`, and `processPendingDeposits_postponed`, test that result.
  The new field `statusOk`, and a new conclusion of `processPendingDeposits_postponed`, say that the status of each deposit read succeeds.
  The new `addValidatorToRegistry_size_lt` says that a new validator joins a registry of fewer than 2^64 validators.
- The FFG theorems on the beacon chain now take their votes from the attestations that blocks apply, instead of from any data that some signature verifies on ([#1888](https://github.com/ethereum/EthLib/issues/1888)).
  Under the BLS checks a verifying signature exists for every data that a registered key can sign, so the old votes did not say who voted.
  No C export or Python function changes.
  In Lean, `SignedVote`, `TargetFlagsSigned` and `PendingSigned` are gone, with their lemmas, `voteFrame_processOperations` and the two `of_stateTransition` lemmas of the flags and the pending attestations.
  The new `attestationVotes` and `blockVotes` name the votes that an attestation and a block cast, and `TargetFlagsVoted` and the new `PendingVoted` take a set of such votes.
  `VoteFrame` drops its configuration, its signature checks and its field `signed`, and `voteFrame_processAttestation` and `voteFrame_processBlock` give the votes of the step by name; the latter takes the preset bound `apart`.
  The slot and upgrade lemmas of the flags and the pending attestations no longer take a bound on the registry.
  The link and slack theorems of `FfgJustification.lean` and `FfgSlack.lean` take the vote set and a hypothesis that the votes of the model hold it, with no slot condition.
  `SlackChainInvariant` drops its configuration, its signature checks and its field `known`, takes the vote set, and uses its votes in the model; `SlackStepHypotheses` replaces `contains` by `applied`, on the new `blockStepVotes`.
  `runVotes` drops its argument `block` and now holds the beacon votes that the block steps of a run cast, so a caller wraps it in `ffgVotes block`.
  `ForkVersionsKnown` is gone with its lemmas, and `initializeBeaconStateFromEth1_target` becomes `JustifiedEarly.of_initializeBeaconStateFromEth1`, which gives only the equal justified checkpoints.
  `TargetFlagAt.of_flagsKeptOrZero` moves to `Upgrade.lean`.
- The theorem that an attestation keeps the registry and the RANDAO mixes now holds at every fork ([#1888](https://github.com/ethereum/EthLib/issues/1888)).
  No C export or Python function changes.
  In Lean, `processAttestation_registry` drops its argument `before : fork < .altair`, so a caller removes it.
- From Gloas, builder deposits, exits and onboarding, ejections, slashing penalties, attestation committee counts and active-validator reads now fail where a position of 2^64 or more would become a 64-bit index ([#1883](https://github.com/ethereum/EthLib/issues/1883)).
  Such a position used to wrap modulo 2^64, so the step read or wrote another validator or builder.
  The registry updates, the slashing penalties, the effective-balance updates and the genesis activations read and write each validator at its plain position, as the specification indexes the registry with a Python integer.
  No C export or Python function changes.
  In Lean, `addBuilderToRegistry` now returns an `Except TransitionError`; bind its result, and pass a successful return to `builderBalanceSum_addBuilderToRegistry`.
  The new `getValidatorAt`, `getBalanceAt` and `BeaconState.setValidatorAt` read and write at a plain position, and `getValidator_eq_getValidatorAt`, `getBalance_eq_getBalanceAt` and `setValidator_eq_setValidatorAt` relate them to the index forms.
  `EpochFrameLaws` replaces its `setValidator` field by a `setValidatorAt` field, and the theorem `EpochFrameLaws.setValidator` gives the index form; `EpochFrameLaws.setValidatorAt_of_sameBalance`, `frame_setValidatorAt_of_whole`, `activeStep_setValidatorAt` and `sameSizes_setValidatorAt` are new.
  `KeysKept`, `Frame.keysKept` and `UpgradeFrame.keysKept` are gone, as no theorem read them ([#1908](https://github.com/ethereum/EthLib/issues/1908)); `advanceSlot_keys` becomes `advanceSlot_kept`, without the key conjunct.
  The setter laws of `EpochFrameLaws` and the frame lemmas of validator writes no longer take a key equality, and the `_of_whole` forms no longer take the old validator.
  `activeKept_processEpoch`, `activeKept_processBlock`, `activeKept_advanceSlot`, `ChainStep.activeKept`, `activeKept_of_chainSteps`, `processBlock_attestationSplit`, `voteFrame_processBlock`, `committeesKept_processBlock`, `committeesKept_advanceSlot`, `RunKept.committeesKept`, `slackJustifiedCheckpoints_chainRoot_of_chainSteps`, `slackFinalized_chainRoot_of_chainSteps` and `processEffectiveBalanceUpdates_effectiveBalance` drop their registry-size argument.
  `SlackStepBounds` drops its field `small`, and the field `RunKept.active` no longer takes a registry bound.
  `getTotalActiveBalance` reads the checked active indices.
  The new `getActiveValidatorIndicesChecked` converts each active position with `ofNatChecked`, as the specification builds each index, and the new `getCommitteeCountPerSlotChecked` also converts their count.
  `getActiveValidatorIndicesChecked_eq_ok_iff` replaces `getActiveValidatorIndices_eq_mapM_ofNatChecked`, and `getTotalActiveBalance_ne_indexOutOfRange` drops its registry bound.
  New lemmas on the checked read: `getActiveValidatorIndicesChecked_ok`, `_of_size_le`, `_of_within`, `_of_attesterShuffle`, `_error` and `_eq_error`, `lt_of_getActiveValidatorIndicesChecked_ok`, `sorted_of_getActiveValidatorIndicesChecked_ok`, `mem_iff_of_getActiveValidatorIndicesChecked_ok` and `ActiveKept.getActiveValidatorIndicesChecked_eq`.
  New lemmas on the checked count: `getCommitteeCountPerSlotChecked_of_within` and `getCommitteeCountPerSlotChecked_ok`; in `Base`, `ofNatChecked_toNat`, `mapM_ofNatChecked_eq_ok_iff` and `mapM_ofNatChecked_error`.
  `getValidatorAt_eq_ok_iff`, `getBalanceAt_eq_ok_iff` and `committeePositions_ne_nil` are new.
  The new `committeeCountOf` gives the committee count for a number of active validators, so the checked count converts the length of the checked list without a second pass over the registry.
  `CommitteesKept.of_seed` also takes the equality of the checked active indices of the two states.
  `proposerCandidates` takes the checked active indices instead of the epoch, and `proposerCandidates_spec` places each candidate among them.
  `getEligibleValidatorIndices_sorted`, `getEligibleValidatorIndices_ok` and `processInactivityUpdates_scores` drop their registry bound: the new `getEligibleValidatorIndices_fits` bounds each eligible position of a successful computation, and the new `validatorPositions_sorted_of_fits` sorts positions under such a bound.
  The new `depositTargetStatus_ne_indexOutOfRange` states that the status of a deposit target never fails on an index, through the new `getElem?_toNat_eq_of_ofNatChecked`.
  `exists_mem_getBeaconCommittee` takes a successful checked active-index read, and `attestationCommitteesSize_of_attesterShuffle` takes a successful checked committee-count read.
  `attestationCommitteesSize_cons` includes that count check on its right side.
- From Gloas, a deposit, a withdrawal or consolidation request, or a sync aggregate now fails where a registry position of 2^64 or more would become a validator index ([#1883](https://github.com/ethereum/EthLib/issues/1883)).
  Such a position used to wrap modulo 2^64, so a deposit at 2^64 validators overwrote validator 0.
  The step now fails with the accessor error `arith overflow`, as the specification fails to build a `ValidatorIndex` there.
  Before Gloas the registry holds at most 2^40 validators, so nothing changes there.
  No C export or Python function changes.
  In Lean, the new `Base.Uint64.ofNatChecked` converts a natural number to a `UInt64`, and fails with an overflow at 2^64 or more.
  `getIndexForNewValidator` now returns an `Except AccessorError ValidatorIndex`, and `queueConsolidation` takes the index of the source in place of its position.
  `addValidatorToRegistry_validators_eq_push`, `addValidatorToRegistry_push`, `activeStep_addValidatorToRegistry` and the deposit theorems of `Proofs.Transition.Operations` and `Proofs.Transition.EpochPending` no longer take a bound on the size of the registry.
  The fields `used`, `appliedFilter` and `movedFilter` of `PassPendingDepositsFacts` no longer take a bound either.
  `frame_queueConsolidation`, `sameSizes_queueConsolidation` and `payloadInputs_queueConsolidation` take the index of the source in place of its position.
- The exact change of the supply of ether across a transaction is now proved at every fork, with the burns of SELFDESTRUCT and the deleted balances as terms fixed by the run ([#1793](https://github.com/ethereum/EthLib/issues/1793)).
  No C export or Python function changes.
  In Lean, the rules of a relation of frames split in two: `OrdinaryStepRules` holds the rules of every write but SELFDESTRUCT, and `StepRules` extends it with the rule of SELFDESTRUCT.
  The lemmas `sameContext`, `refl` and `lift`, and those of SSTORE, TSTORE, the calls, the creations and the instructions that send a message, move from the `StepRules` namespace to `OrdinaryStepRules`.
  So a qualified name changes, while the dot notation on a `StepRules` value still works.
  `OrdinaryStepRules.instruction` takes a proof that the opcode is not SELFDESTRUCT, and `StepRules.instruction` is gone; `StepRules.step` covers every instruction.
  The new `OrdinaryStepRules.step` concludes that a step either runs SELFDESTRUCT, as the new `RunsSelfdestruct` says, or keeps the relation.
  `runTransaction_eq_ok` now concludes `TransactionRun`, a definition that unfolds to the same seven equations, and `TransactionRun.unique` proves that its values are fixed by the transaction and its output.
  The new `processMessage_frame_byKind` runs the induction over messages for any fact about the frame of a call, and `processMessage_rel_byKind` keeps its statement and now follows from it.
- The fork choice now rejects an attestation whose committees are not those of its slot, a step of the safety proof of the fast confirmation rule ([#1458](https://github.com/ethereum/EthLib/issues/1458)).
  It runs the committee check of block processing in the state of the target, with one aggregation bit for each member of the committees.
  Before Electra the index must be below the count of committees of the slot.
  From Electra each index of the committee bits must be below that count, each of those committees must have a bit set, and the index of the attestation must be 0 before Gloas.
  Before, a committee index past that count named a committee of a later slot of the same epoch, or none, so a validator could vote for a slot before its own.
  Gossip validation and block processing already rejected such an attestation.
  The rejection is the fork choice error `transition`, which carries the error of the check, such as `committeeIndexOutOfRange`; a failed shuffle is now reported there too.
  No signature of a C export or Python function changes, but an `attestation` step of `fork_choice` now rejects these attestations, and so does a `block` step that carries one.
- The safety threshold of the fast confirmation rule now fails when the discount for empty slots exceeds the weight of the committees since the parent ([#1832](https://github.com/ethereum/EthLib/issues/1832)).
  It fails with the new fork choice error `supportDiscountAboveMaximum`, of code 53, where it used to return half of what was left, or 0.
  A block at or before the current slot never reaches that error, and a proof shows it.
- The theorems on the four system contracts of EIP-4788, EIP-2935, EIP-7002 and EIP-7251 now hold from Glamsterdam too, with the state gas meter of EIP-8037 ([#1861](https://github.com/ethereum/EthLib/pull/1861)).
  No C export or Python function changes.
  In Lean, each `systemCall_set` and `systemCall_dequeue`, with its `spec_set` or `spec_dequeue`, no longer requires a fork before Glamsterdam.
  The one-counter gas premises of `spec_set` and `spec_dequeue` are multiplied by `storageGasScale fork`, which is 1 before Glamsterdam and 5 from it.
  `RequestQueue.sstore_writes` and `RequestQueue.sstore_then` change the same way, and their continuation must hold with up to 22,100 gas times that factor less.
  The SSTORE rules `sstoreStep_eq`, `sstoreG`, `sstore` and `sstore_of_account` of the EVM logic now hold from Berlin at every fork.
  They charge `sstoreTotalCost`, the price and the state gas of the write, where they charged `sstoreCost`.
  Before Glamsterdam, `sstoreTotalCost_of_lt` turns that charge back into the price.
  `SystemContract.systemCall_of_spec` and `SystemContract.systemCall_of_writesStorage` no longer require a fork before Glamsterdam, and take a proof that the code passes `SupportedCode` from Glamsterdam.
- Each fork upgrade now gives one upgrade frame, and the invariant across the upgrade follows from it ([#1841](https://github.com/ethereum/EthLib/pull/1841) and [#1851](https://github.com/ethereum/EthLib/pull/1851)).
  `UpgradeFrame` now also keeps the finalized checkpoint, and it carries the balance count and the exit order of the validators.
  So a caller that builds one supplies the three new fields, and `UpgradeFrame.of_carried` takes the finalized checkpoint and the number of balances as new premises.
  `UpgradeFrame`, its constructors, `UpgradeFrame.invariant` and the frame of each upgrade are in `EthLib.Consensus.Proofs.Transition.Upgrade`, and `upgradeFrame_upgradeNext` is in `EthLib.Consensus.Proofs.Transition.ForkBoundary`.
  `upgradeFrame_carryFields` no longer takes a proof that the fork is at least Altair.
  `Invariant.of_carried` is gone; `UpgradeFrame.invariant` replaces it.
  No statement of an invariant theorem changes, and no C export or Python function changes.
- The fast confirmation rule now weighs the committees of a range of slots exactly, in place of an average per slot ([#1828](https://github.com/ethereum/EthLib/issues/1828)).
  Each active member of the committees counts once, by its effective balance in the source of balances, and a range with a whole epoch still weighs the total active balance.
  The average did not bound a given committee, so the rule could confirm a block that an attack then reorgs.
  The rule can now confirm fewer blocks, or more, than before, and some pinned fast confirmation vectors expect the old answers.
  `estimateCommitteeWeightBetweenSlots`, `adjustCommitteeWeightEstimateToEnsureSafety` and `COMMITTEE_WEIGHT_ESTIMATION_ADJUSTMENT_FACTOR` are gone; the new `Store.computeCommitteeWeightBetweenSlots` replaces them, and takes the head and the source of balances.
  `Store.computeCommitteeWeightAndMembers` also returns the members it reads, and `Store.getEquivocationScoreOf` weighs the equivocators of a given set.
  No C export or Python function changes.
- A contract creation now fails at an address with non-empty storage, at every fork, as [EIP-7610](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7610.md#specification) asks ([#1823](https://github.com/ethereum/EthLib/issues/1823)).
  Before, such a creation wiped the storage and ran the init code.
  It now fails exactly like a creation at an address with code or a nonce, as [EIP-684](https://eips.ethereum.org/EIPS/eip-684#specification) asks: a creation transaction ends with `addressCollision`, and CREATE or CREATE2 takes the gas of the message and pushes 0.
  So a block with such a creation can now have another gas used, another state root, or be rejected.
  From Glamsterdam, CREATE or CREATE2 that collides gets back the state gas of the new account that it paid, as [EIP-8037](https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-new-accounts) asks of a collision.
  Only a target with storage but no nonce, code or balance paid any.
  `accountDeployable` also requires empty storage, through the new `accountHasStorage`.
  The rules `createKind_stored`, `create_stored` and `create2_stored` take a new hypothesis: no fact of a slot gives the new address a word other than zero.
  The new theorems `accountHasStorage_eq_true_iff`, `accountDeployable_eq_true_iff` and `accountDeployable_congr` state the rule.
- The Engine API now models `engine_getPayloadV1` to `engine_getPayloadV6` ([#1848](https://github.com/ethereum/EthLib/pull/1848)).
  `EngineError` has a new constructor, `unknownPayload`, with code 38001, so an exhaustive match on it needs a new case.
  A store of completed builds holds the result of the payload build, its blobs bundle, the override flag and, from Glamsterdam, the block access list.
  The returned payload must give back the stored block hash, with the stored requests and access list.
  From version 3 the commitments of the bundle must hash to the blob hashes of the block, in order, and its proofs must verify.
  The C export `eth_engine_get_payload` takes the configuration, the store and the request.
  Each entry of the store holds the payload ID, the fork and the four results of `eth_engine_build_payload`.
  Then come the network forms of the blob transactions, the flag and the access list.
  In Python, `engine.get_payload` takes the configuration, the store, the method and its parameters.
  The payload ID has one type, `PayloadId`, which the forkchoice update also returns.
  The network check of a blob transaction now runs `validateBlobs` on its lists, so `countsMatch` is `blobCountsMatch` on its fields.
- The forkchoice update now checks the timestamp of payload attributes, on an applied valid head ([#1479](https://github.com/ethereum/EthLib/issues/1479)).
  A known payload holds the number and the timestamp of its block, so `KnownPayload` has two new fields, `number` and `timestamp`.
  `forkchoiceUpdatedCall` takes the chain configuration first, and returns the attributes at the fork of their timestamp.
  Attributes of a fork that the version does not take now give code 38005, `unsupportedFork`.
  Version 1 takes Paris, version 2 Paris and Shapella, version 3 Dencun to BPO5, and version 4 Glamsterdam.
  Version 2 with the structure of version 1 from Shapella, or of version 2 before it, gives code 38003.
  So do attributes whose timestamp is not above that of the head.
  The C export `eth_engine_forkchoice_updated` takes the configuration first, and each payload of the tree needs `number` and `timestamp`.
  In Python, `engine.forkchoice_updated` takes the configuration first.
- The forkchoice update now models `engine_forkchoiceUpdatedV4`, and it checks the structure of the payload attributes on an applied valid head ([#1478](https://github.com/ethereum/EthLib/issues/1478)).
  Attributes that fit no structure of the version now give code 38003, `invalidPayloadAttributes`, where any object gave code 0 before.
  Attributes that fit still give code 0, since no payload build is specified.
  A wrong number of parameters now has the reason `params: got N, expected 2`, or `2 or 3` for version 4, in place of `params: not 2 values`.
  `forkchoiceUpdatedParams` takes the version first and returns the attributes as JSON, or `none`, in place of a flag.
  `EngineError` has a new constructor, `invalidPayloadAttributes`, with code 38003.
- `MIN_REQUEST_LIMIT`, the fewest versioned hashes that `engine_getBlobs` must take in one request, is now `MIN_BLOBS_REQUEST_LIMIT`.
  Its value stays 128, and no C export or Python function changes.
- The optimistic store now holds its head as a fork choice node, a root and the status of its payload, in place of the root of the head block ([#1475](https://github.com/ethereum/EthLib/issues/1475)).
  From Gloas, the optimism of the head reads the payload that the status names, so it can fail as a payload chain does, and it returns an `Except`.
  The C export `eth_consensus_is_optimistic_node` takes the code of that status after the head root: 0 empty, 1 full and 2 pending.
  In Python, `consensus.is_optimistic_node` takes it as the keyword `head_payload_status`, 2 by default, so a call before Gloas gets the same answer as before.
  The latest verified ancestor now takes a fork choice node; before Gloas it reads only the root.
  The C export `eth_consensus_latest_verified_ancestor` takes the code of the status after the root, and `consensus.latest_verified_ancestor` takes it as the keyword `payload_status`, 2 by default.
  The latest verified ancestor and the optimistic node now run at Gloas.
  The theorem `latestVerifiedAncestor_of_glamsterdam` now states the Gloas answer, no longer a failure.
  The optimistic node then fails when the head is not optimistic, since its second case is not yet specified.
- `compute_min_epochs_for_block_requests` now takes the fork, and from Gloas it applies a formula derived from the [weak subjectivity period of EIP-8061](https://eips.ethereum.org/EIPS/eip-8061#weak-subjectivity-period).
  Before, every fork got the Phase 0 value: 33024 epochs on mainnet, where Gloas asks for 14299.
  `Config.computeMinEpochsForBlockRequests` takes the fork as a new argument.
  The C export `eth_consensus_compute_min_epochs_for_block_requests` reads the configuration and the fork as a pair, as `eth_consensus_gossip_topics` does.
  In Python, `consensus.compute_min_epochs_for_block_requests` takes the fork first, then the configuration, `mainnet` by default.
- `NoiseError` now gives its own code to each failure of the local identity secret, of signing and of the saved remote message, in the libp2p Noise handshake ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  Before, a failure of the secret or of signing had code 9, the code of an invalid remote identity.
  An identity secret that is 0, or at least the secp256k1 group order, now gives code 11, `identitySecret`.
  A failure of ECDSA signing with that secret gives code 12, `signing`.
  Completion of a state whose saved remote message is missing, or does not match the state, gives code 13, `savedRemote`.
  Before, such a state gave the error of the failed step: code 1, 3, 4, 6, 7, 8 or 9.
  Code 9 now means only a remote identity that fails to authenticate.
- The libp2p Noise handshake gives the identity secret, the chaining key and the handshake hash their own types, apart from the type of the X25519 keys ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  The secp256k1 identity secret of `writeLibp2p` and `makePayload` is a scalar `Secp256k1.Fn`, in place of 32 bytes.
  `Libp2p.publicKey` and `Libp2p.sign` take that scalar too, and the exports read it from 32 big-endian bytes whose value must be below the group order.
  The chaining key and the handshake hash of `SymmetricState` have the types `ChainingKey` and `HandshakeHash`, and `hkdf2` takes a `ChainingKey`.
  The C exports and the Python functions keep their signatures: they take the secret and return the chaining key and the hash as 32 bytes.
  `writeLibp2p` now rejects a zero identity secret before every other check, on every message, message 1 included.
  The C export `eth_noise_libp2p_write`, and `noise_libp2p_write` in Python, give code 11 for a secret of 0 or at least the group order.
  Before, a write at step 0 ignored the secret: message 1 succeeded, and a responder writing out of turn got code 1, `wrongPhase`, or code 10, `firstMessageExtensions`.
- The libp2p Noise state now stores the authenticated remote, in place of the encrypted remote message and the state before it ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  Completion returns that remote with the transport ciphers, and reads no message.
  It returns `Remote × CipherState × CipherState`.
  `Libp2pState.remoteMessage` is now `Libp2pState.remote`, a `Remote` with the static key, the identity point, the signature and the extensions.
  `AuthenticatedRemote`, `RemoteInfo` and `remoteInfo` are removed, and `authenticatePayload` returns a `Remote`.
  `writeLibp2p` no longer runs completion after message 3.
  The Python state of `noise_libp2p_*` holds the remote as `(static_key, public_key, signature, extensions)`, or `None`, in place of the saved message and its state.
  Completion checks that the stored remote has the remote static key of the handshake, and no longer verifies its signature.
  Code 13, `savedRemote`, now means that at completion the state holds no remote, or one whose static key is not the remote static key of the handshake.
  `readLibp2p_authenticates` now concludes that the new state stores the authenticated `Remote`.
  The theorems `complete_authenticates` and `complete_peerId` are replaced by `complete_ok` and the `Produced` theorems, and `authenticatePayload_decode` by `authenticatePayload_ok`.
  The C exports and Python functions that take a libp2p state, to write, read or complete, also give code 13 when the stored public key does not decode.
- `ethlib.networking.noise` now exports short typed wrappers in place of the raw `noise_*` names of the extension ([#1657](https://github.com/ethereum/EthLib/issues/1657)).
  `noise_initialize` is now `initialize`, `noise_cipher_encrypt` is `cipher_encrypt`, `noise_libp2p_complete` is `libp2p_complete`, and so on; `libp2p_write` takes `extensions=None` by default.
  The package also exports the type aliases of its states, `CipherState`, `HandshakeState`, `Remote`, `Libp2pState`, `Identity` and `Completion`, which `lake exe gen-bindings` writes from Lean, and `NoiseError`.
  The extension methods keep their names and signatures.
- A chain configuration now holds the address of its deposit contract, and the deposit requests of a block come from that address ([#1486](https://github.com/ethereum/EthLib/issues/1486)).
  Before, every chain read deposits from the mainnet address, so a chain with another deposit contract, such as Sepolia, got no deposit request.
  The configuration that the exports read as JSON, or as a Python `dict`, must give `depositContractAddress`: `0x` and forty hex digits, or 20 bytes in Python.
  A configuration without it is rejected with `config: no depositContractAddress`.
  `depositRequests`, the C export `eth_block_deposit_requests` and `blocks.deposit_requests` in Python take the address first.
- The output of the VRF tree at index `i` now hashes the index before the secret: `keccak256(PQ_VRF_OUTPUT | LE32(i) | s)` ([#1652](https://github.com/ethereum/EthLib/pull/1652)).
  Every output changes, for every root, index and seed.
  Roots and openings are unchanged, so an existing opening still verifies, but returns a different output.
  `verify`, `verifyBytes` and `evaluate` keep their arguments, and `outputHash` takes the index.
  Before, one secret placed at every leaf gave every index the same output, which the holder could choose.
  A new `mixOutput`, the C export `eth_vrf_mix` and `vrf.mix` in Python hash an output with randomness.
  A selection must compare that mixed value, with randomness revealed after the root is registered.
- `engine_forkchoiceUpdated` now applies step 2 of its specification ([#1018](https://github.com/ethereum/EthLib/pull/1018)).
  The execution layer may know a finalized block from an earlier update.
  A valid head below that block is answered `VALID`, and the forkchoice state is not checked.
  The Lean function and the C export `eth_engine_forkchoice_updated` take that block as a new argument, between the tree and the request.
  The C export reads it as JSON text: a block hash, or `null` for none.
  In Python, `engine.forkchoice_updated` takes it as the keyword `finalized`, `None` by default, so a call without it gets the same answer as before.
- `engine_forkchoiceUpdated` with payload attributes now answers a syncing head, an invalid head and a head below the known finalized block, since no payload build begins there ([#1018](https://github.com/ethereum/EthLib/pull/1018)).
  A request that would select a new head with payload attributes is still refused with code 0, because the build is not specified.
- The shuffle errors of `ConsensusError` now have the codes 201 to 204, in place of 1 to 4 ([#1087](https://github.com/ethereum/EthLib/pull/1087)).
  The custody errors already had the codes 1 to 3 in the same class, so a code did not name one error.
  A caller that tests `code == 1` for an index at or past the count now tests `code == 201`.
  The new code 204 is a count above 2^40.
- `compute_shuffled_index` and `compute_shuffled_permutation` now fail for a count above 2^40, as the consensus specification does ([#1072](https://github.com/ethereum/EthLib/pull/1072) and [#1087](https://github.com/ethereum/EthLib/pull/1087)).
  Before, the index wrapped a bucket number that does not fit in 4 bytes and returned a value.
- The C export `eth_engine_forkchoice_updated` now rejects a tree of known payloads that names one block hash twice, with code 0 ([#1102](https://github.com/ethereum/EthLib/pull/1102)).
  Before, it answered from the first entry of that hash and ignored the second.
- The Ethash exports, the CRC-32 and CRC-32C exports and the precompile price now take and return typed values ([#1516](https://github.com/ethereum/EthLib/pull/1516)).
  A number crosses as a Python `int`, and the proof-of-work function returns its mix digest and its result as a pair.
  The C exports take the tuple of their arguments as one value, as `eth_consensus_fork_choice` does.
  In Python, an argument that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError` before.
  Examples are a `str` given for bytes and a `bool` given for an `int`.
  A negative number raises `ValueError`, where it raised `OverflowError`.
  An address of 2^64 or more has no precompile, so its price raises `PrecompileError`, where it raised `OverflowError`.
- The EVM word and memory exports, the CREATE address, the fee exports and the block difficulty now take and return typed values ([#1524](https://github.com/ethereum/EthLib/pull/1524)).
  `eth_evm_word_op` takes the opcode and a list of at most three operands, each an `int` below 2^256.
  `eth_evm_extend_memory` replaces `eth_evm_extend_memory_cost` and `eth_evm_extend_memory_expand_by`, and returns the price and the growth as a pair.
  Each range is a pair of two words.
  The base fee and the fake exponential now return a result that can fail, as every typed export does.
  The error codes 101 and 102 of `EvmError` are gone, since no export reads the lengths of operands or ranges now.
  In Python, an argument that Lean cannot read raises the error class of the method with code 0.
  Examples are an operand, a range word or an opcode out of range, more than three operands, a `bool` given for an `int` and `bytes` given for a fork name.
  Before, these raised `OverflowError`, `ValueError`, `TypeError` or `AttributeError`.
  A negative number raises `ValueError`, where it raised `OverflowError`.
- The transaction check, the check against a block, the settlement and the run now take and return typed values ([#1529](https://github.com/ethereum/EthLib/pull/1529)).
  The C exports `eth_tx_check`, `eth_tx_check_in_block`, `eth_tx_settle` and `eth_tx_run` take the tuple of their arguments as one value.
  They return tuples where they returned fixed-width bytes or an RLP list.
  In Python, `Run.accounts` holds each nonce, balance and storage value as an `int`, where they were the bytes of RLP scalars.
  Each account and each storage slot is a tuple, where it was a list.
  An argument that Lean cannot read raises `TransactionError` with code 0, where some raised `TypeError` or `OverflowError`.
  Examples are a chain ID of 2^64 or more, a `bool` given for an `int` and `bytes` given for a fork name.
  A negative number raises `ValueError`, where it raised `OverflowError`.
- The header checks, the genesis block, the typed RLP decoder and the hex-prefix encoding now take typed values ([#1542](https://github.com/ethereum/EthLib/pull/1542)).
  The C exports `eth_block_validate_header`, `eth_block_check_header`, `eth_genesis_block`, `eth_rlp_decode_as` and `eth_trie_hex_prefix` take the tuple of their arguments as one value.
  The header checks take the blob schedules as pairs of four integers, and return `None`.
  `eth_genesis_block` takes the fields of the header as one tuple, and `eth_trie_hex_prefix` takes a list of nibbles.
  `eth_rlp_decode_as` returns the value itself, such as an `int`, a `bool` or `None` for a contract creation.
  A new export, `eth_pow_chain_forks`, writes the RLP form of the forks of a chain, which `chain_forks` returns.
  In Python, an argument that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
  Examples are `bytes` given for a fork name or for the kind of `rlp.decode_as`, and an `int` given for the `is_leaf` flag.
  A nibble of 16 or more raises `TrieError` with code 0, where one of 256 or more raised `OverflowError`.
  A negative number raises `ValueError`, where some raised `OverflowError`.
- Every typed export reads a pair, such as a memory range or a blob schedule, from a Python list as from a tuple ([#1542](https://github.com/ethereum/EthLib/pull/1542)).
- The networking exports that returned JSON text, packed records or joined bytes now return typed values ([#1547](https://github.com/ethereum/EthLib/pull/1547)).
  These are the discv5 key derivation, packet, message, WHOAREYOU and handshake exports, the fork identifier, the consensus entries and `eth` entry of a record, the RLPx answer and the req/resp response chunk.
  Their C exports take the tuple of their arguments as one value, and return a typed value where they returned bytes.
  Two new exports, `eth_fork_id_schedule` and `eth_fork_id_encode`, write the RLP schedule and fork identifier that `forkid.schedule` and `forkid.encode` return.
  `forkid.encode` now requires a 4-byte hash and a next fork below 2^64, as the fork identifier types them.
  The discv5 `dict` results keep their keys and values, in the order of the packet rather than sorted.
  In Python, an argument of the right Python type that Lean rejects raises the error class of the method with code 0, where some raised `TypeError`, `OverflowError` or `AttributeError`.
  Examples are a block number of 2^64, `bytes` given for a fork name, and `str` given for bytes.
  A negative number raises `ValueError`, where it raised `OverflowError`, and a value that cannot cross, such as a `bytearray`, still raises `TypeError`.
  `rlpx.SECRETS_SIZE` is now read from Lean.
- The consensus presets, configurations and parameters, and the active fork of a configured chain, now take and return typed values ([#1548](https://github.com/ethereum/EthLib/pull/1548)).
  The C exports `eth_consensus_preset`, `eth_consensus_config`, `eth_consensus_parameters` and `eth_active_fork` take the tuple of their arguments as one value.
  The first three return a `dict`, where they returned JSON text.
  An integer in that `dict` is an `int`, where it was a string of decimal digits.
  `eth_active_fork` takes the chain configuration as a `dict` with the keys of its JSON form, and returns the name of the fork or `None`.
  In Python, an argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
  An example is `bytes` given for a name.
  A timestamp or a block number of 2^64 or more given to `chain.active_fork` raises `ChainError` with code 0, where it raised `OverflowError`.
  A `bool` given there raises `ChainError` with code 0, where it read as 0 or 1.
  A negative number raises `ValueError`, where it raised `OverflowError`.
- A replacement of a 64-bit value of a consensus configuration may now be an `int`, where it had to be a string ([#1548](https://github.com/ethereum/EthLib/pull/1548)).
- The Engine API exports, the block state transition and the check of an `eth_getProof` answer now take typed values in place of JSON text ([#1549](https://github.com/ethereum/EthLib/pull/1549)).
  The C exports `eth_engine_new_payload`, `eth_engine_forkchoice_updated`, `eth_engine_prepare_execution_payload`, `eth_engine_new_payload_on_chain`, `eth_state_transition` and `eth_trie_verify_account_proof` take the tuple of their arguments as one value.
  A configuration, a request or an answer crosses as the Python value of its JSON, and the first three return the value of the JSON of their answer.
  `eth_engine_new_payload_on_chain` returns the status with the header and the accounts in RLP, or `None` twice, where it returned an RLP list.
  `eth_trie_verify_account_proof` returns `None` for an absent account, or one bool for each slot, and Lean reads the patterns of the fields of the answer, where Python read them.
  In Python, `bytes` inside one of these values now crosses as `0x` hex text, where `json.dumps` refused it.
  A `float`, a negative `int` or a `dict` key that is not a `str` raises `TypeError` or `ValueError`, where `json.dumps` wrote it.
  An argument of the right Python type that Lean rejects raises the error class of the method with code 0, where some raised `TypeError`.
  Examples are `str` given for the state, and `1` given for `check_seal`.
  A field of an `eth_getProof` answer that is missing or out of its pattern raises `TrieError` with code 0, where it raised `KeyError` or `ValueError`.
- On a free-threaded build of CPython, such as 3.14t, importing the extension now leaves the GIL disabled ([#1372](https://github.com/ethereum/EthLib/issues/1372)).
  Threads may call the exports at the same time, and a list that another thread changes during a call is read as a snapshot.
- The consensus gossip and req/resp lists, the subscribed subnets and the SSZ root exports now take and return typed values ([#1551](https://github.com/ethereum/EthLib/pull/1551)).
  The C exports `eth_consensus_gossip_topics`, `eth_consensus_reqresp_protocol_ids`, `eth_consensus_reqresp_parse_protocol_id`, `eth_consensus_reqresp_request_bounds`, `eth_consensus_reqresp_response_bounds` and `eth_consensus_compute_subscribed_subnets` take the tuple of their arguments as one value.
  So do `eth_consensus_ssz_static`, `eth_consensus_reqresp_message`, `eth_consensus_merkle_proof` and `eth_pq_keys_ssz`.
  A list comes back as a list, the subscribed subnets as a list of `int`, and a pair as a tuple, where each came back as JSON text.
  The three SSZ exports return the root and the bytes as a pair, where they returned the two joined.
  `eth_consensus_merkle_proof` returns the node and the list of its siblings, and `eth_consensus_compute_subscribed_subnets` takes the node ID as an `int`.
  In Python, a node ID of 2^256 or more, or an epoch or a generalized index of 2^64 or more, raises the error class of the method with code 0, where it raised `OverflowError`.
  A `bool` given for one of them raises the same error, where it read as 0 or 1.
  A negative number raises `ValueError`, where it raised `OverflowError`.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
- The custody exports, the shuffle, the matrix, the shape check of a data column sidecar and the sidecars of a block now take and return typed values ([#1552](https://github.com/ethereum/EthLib/pull/1552)).
  The C exports `eth_consensus_get_custody_groups`, `eth_consensus_compute_columns_for_custody_group`, `eth_consensus_compute_shuffled_permutation`, `eth_consensus_compute_shuffled_index` and `eth_consensus_get_validators_custody_requirement` take the tuple of their arguments as one value.
  So do `eth_consensus_verify_data_column_sidecar`, `eth_consensus_compute_matrix`, `eth_consensus_recover_matrix` and the two exports of the sidecars of a block.
  A list of groups, columns or positions comes back as a list of `int`, where it came back as JSON text.
  A node ID crosses as an `int`, a validator index as an `int`, and a configuration replacement as a `dict`.
  The blobs and the matrix entries cross as a list of bytes, where they crossed joined in one byte string.
  The sidecars come back as a list of bytes, where they came back as the SSZ encoding of a list.
  A row of cells crosses as a pair of lists, and a row with another count than 128 cells and 128 proofs raises `SszError` with code 0.
  In Python, a node ID of 2^256 or more, or a count, group or index of 2^64 or more, raises the error class of the method with code 0.
  A `bool` or a `str` given for one of these numbers raises the same error.
  Before, these cases raised `OverflowError` or `TypeError`, or read a `bool` as 0 or 1, and for a validator index they raised `struct.error`.
  A negative number raises `ValueError`.
  A seed, a blob, a matrix entry, or a cell or proof of a row, of the wrong length, raises the error class of the method with code 0 and the message `expected N bytes, got M`.
  A `bytearray` or a `memoryview` given for bytes raises `TypeError`, where some were read as bytes.
- The consensus transition exports now take typed values ([#1556](https://github.com/ethereum/EthLib/pull/1556)).
  These are the block operations, the epoch steps, the slots and the state transitions of one block or of several blocks.
  They are also the upgrades, the rewards and penalties, the genesis exports and the weak subjectivity exports.
  Their C exports take the tuple of their arguments as one value, in the order they had.
  A configuration replacement crosses as a `dict`, where it crossed as JSON text, and any other value raises the error class of the method with code 0.
  In a replacement, a negative `int` or a `float` raises `ValueError` or `TypeError` from the converter, and `bytes` crosses as `0x` hex.
  The names of the kinds of deltas and of the forks of the blocks cross as `str`.
  The deposits of the genesis cross as a list of bytes, one deposit each, where they crossed joined in one byte string.
  A hash of the Eth1 block of another length than 32 bytes raises `TransitionError` with code 0 and the message `expected 32 bytes, got N`, where the message began with `input rejected`.
  Every argument is read before the names, so an argument that Lean cannot read is reported before an unknown preset.
  In Python, a slot count or an Eth1 timestamp of 2^64 or more, or a negative one, raises an error, where it was read modulo 2^64 without one.
  The times of weak subjectivity of 2^64 or more raise the error class of the method with code 0, where they raised `OverflowError`.
  A negative number raises `ValueError`.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where it raised `TypeError`.
  Examples are `bytes` given for a name and `str` given for a state.
  A `bool` given for a slot count, and `1` or `None` given for `verify`, now raise the same error, where they were read as 0 or 1 or by truthiness.
  The limits of the converter, 2^29 bytes and 2^22 values in one call, now apply to the states and the blocks.
- The honest validator exports that take a state, and the optimistic sync exports of the ancestor and the payload verdicts, now take and return typed values ([#1558](https://github.com/ethereum/EthLib/pull/1558)).
  These are the committee, proposer, sync committee and PTC assignments, the sync committee subnets and the upcoming proposal slots.
  They are also the signature of a duty, the construction of an attestation and of a single attestation, the Eth1 vote, the pending deposit count and the new state root.
  The others are the latest verified ancestor and the two payload verdicts.
  Their C exports take the tuple of their arguments as one value, in the order they had, and a configuration replacement as a `dict`, as the transition exports do.
  The committee assignment comes back as a tuple of the committee, its index and its slot, or `None`, where it came back as JSON text.
  The PTC assignment comes back as an `int` or `None`, and the sync committee subnets and the upcoming proposal slots as a list of `int`, where they came back as JSON text.
  The Eth1 chain crosses as a list of pairs of a timestamp and the SSZ bytes of the Eth1 data, where each block crossed as 80 packed bytes.
  Eth1 data of another length than 72 bytes raises `ProposerError` with code 0, after the fork and the state are read, where it raised `ValueError`.
  The optimistic roots cross and come back as a list of 32-byte roots, where they crossed joined in one byte string.
  A root of another length than 32 bytes raises the error class of the method with code 0 and the message `expected 32 bytes, got N`.
  Before, the message was `a root is 32 bytes, not N` or `a list of roots is 32 bytes each, not N`, and it came after the checks of the name and the fork.
  In Python, an epoch, an index or a timestamp of 2^64 or more raises the error class of the method with code 0, where it raised `OverflowError`, or `struct.error` for an Eth1 timestamp.
  A negative number raises `ValueError`, where it raised `OverflowError` or `struct.error`.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
  An example is `bytes` given for a name or a duty.
  A `bool` given for an index, and `1` or `None` given for `verify`, now raise the same error, where they were read as 0 or 1 or by truthiness.
  A `bytearray` or a `memoryview` given for an optimistic root or for the Eth1 data of a block raises `TypeError`, where it was read as bytes.
- The light client exports that take a configuration now take and return typed values ([#1559](https://github.com/ethereum/EthLib/pull/1559)).
  These are the sync, the light client header of a block, the checks of the proofs of an update, the ranking of two updates, the bootstrap, the update and the fork digest.
  Their C exports take the tuple of their arguments as one value, in the order they had, and a configuration replacement as a `dict`, as the transition exports do.
  The steps of a sync cross as tuples, `("update", fork, slot, data)`, `("force", slot)` and `("upgrade", fork)`, where they crossed packed in one byte string.
  The sync returns, for each step, the pair of the finalized and the optimistic header, each a tuple of a slot and two roots, where it returned 144 bytes for each step.
  The light client header of a block comes back as the pair of the root and the bytes, where the two came back joined.
  An unknown finalized block of an update is `None`, where it was empty bytes; in Python, empty bytes still stand for it.
  A root of another length than 32 bytes raises the error class of the method with code 0 and the message `expected 32 bytes, got N`, where it said `a root has 32 bytes`.
  In Python, a step of an unknown kind raises `LightClientError` with code 0, where it raised `ValueError`.
  A slot of a step of 2^64 or more raises `LightClientError` with code 0, and a negative one `ValueError`, where it raised `OverflowError`.
  An epoch of the fork digest of 2^64 or more raises `SszError` with code 0, and a negative one `ValueError`, where both were read modulo 2^64.
  A `bool` given for a slot or an epoch raises the error class of the method with code 0, where it was read as 0 or 1.
  A `bytearray` or a `memoryview` given for the data of an update raises `TypeError`, where it was read as bytes.
  Every argument is read before the names, so a root of the wrong length is reported before an unknown preset or a fork before Altair.
  The limits of the converter, 2^29 bytes and 2^22 values in one call, now apply to the states, the blocks and the steps.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError`.
- The gossip validation export now takes and returns typed values ([#1561](https://github.com/ethereum/EthLib/pull/1561)).
  Its C export takes the tuple of its arguments as one value, in the order it had, and a configuration replacement as a `dict`, as the transition exports do.
  The blocks after the anchor cross as tuples of a kind, a payload status or `None`, the SSZ bytes and an optional envelope, where they crossed packed in one byte string.
  An envelope of `None` means no envelope, as empty bytes still do.
  A payload status of 255 is now a status, where it meant none; only `None` means none.
  The messages cross as tuples of a time, a subnet, the SSZ bytes and an optional topic, where they crossed packed in one byte string.
  A topic of a message may now be longer than 255 bytes in UTF-8, where it raised `ValueError`.
  The finalized checkpoint crosses as a pair of an epoch and a root, or `None`, where it crossed as 40 bytes, and the topic as a `str`.
  Each outcome comes back as a pair of `valid`, `ignore` or `reject` and its reason or `None`, where it came back packed in one byte string.
  In Python, a block or a message of another length than three or four items raises `ForkChoiceError` with code 0.
  Before, a shorter one raised `ValueError`, and a longer one was read without its extra items.
  A time, a subnet or an epoch of 2^64 or more raises `ForkChoiceError` with code 0, and a negative one `ValueError`, where it raised `OverflowError`.
  A kind or a payload status of 256 or more raises `ForkChoiceError` with code 0, where it raised `ValueError`.
  A `bool` given for one of these numbers, and `1` or `None` given for `verify`, raise the same error, where they were read as 0 or 1 or by truthiness.
  A `bytearray` or a `memoryview` given for the bytes of a block, an envelope or a message raises `TypeError`, where it was read as bytes.
  An argument that crosses to Lean but that Lean cannot read raises the error class of the method with code 0, where some raised `TypeError` or `AttributeError`.
  A root of the finalized checkpoint of another length than 32 bytes raises `ForkChoiceError` with code 0 and the message `expected 32 bytes, got N`, where the message was `the finalized checkpoint is not 40 bytes`.
  Every argument is read before the names, and the limits of the converter, 2^29 bytes and 2^22 values in one call, now apply.
- The generic SSZ exports now take and return typed values ([#1563](https://github.com/ethereum/EthLib/pull/1563)).
  The C exports `eth_ssz_serialize`, `eth_ssz_deserialize` and `eth_ssz_hash_tree_root` take the tuple of their arguments as one value.
  A type and a value cross as the Python values of their tagged form, such as `{"uint": 2}` and `{"uint": 258}`, where they crossed as JSON text.
  `eth_ssz_deserialize` returns the value as a `dict`, where it returned JSON text.
  In Python, `bytes` inside a type or a value now crosses as `0x` hex, where `json.dumps` refused it.
  A `float` or a `dict` key that is not a `str` raises `TypeError`, and a negative `int` raises `ValueError`, where each raised `SszError` with code 0.
  Data that is not `bytes` raises `SszError` with code 0, where it raised `TypeError`.
  The converter reads an argument nested at most 64 levels below it, where 256 SSZ levels were read.
  So a value of more than 31 `seq` or `union` levels raises `ValueError`, and so does a type of more than 32 `vector` or `list` levels or more than 21 `container` levels.
  A value that `deserialize` returns past these bounds, or past the converter budget, cannot be given back to `serialize`.
- The active fork of mainnet and of Hoodi, the seal hash, the proof-of-work check, the gossip message ID and the recent blocks of a chain now cross as typed values ([#1571](https://github.com/ethereum/EthLib/pull/1571)).
  The C exports `eth_mainnet_active_fork`, `eth_hoodi_active_fork`, `eth_pow_seal_hash`, `eth_pow_check` and `eth_gossip_message_id` take the tuple of their arguments as one value.
  A fork crosses as its name, a `str`, where it crossed as UTF-8 bytes, and the active fork comes back as a `str` or `None`, where it came back as bytes.
  `eth_state_transition` and `eth_engine_new_payload_on_chain` take the recent blocks as a list of tuples, where they took one RLP list.
  Each tuple is the fork name, the header in RLP form and the list of the RLP forms of its ommers.
  In Python, `mainnet_active_fork` and `hoodi_active_fork` raise `ChainError` with code 0 for a block number or a timestamp of 2^64 or more.
  They raise `ValueError` for a negative one, where both raised `OverflowError`.
  A `bool` given there raises `ChainError` with code 0, where it was read as 0 or 1.
  A recent block whose header or ommer does not decode raises `BlockError` from `state_transition` and `EngineError` from `new_payload_on_chain`, with code 0, where it raised `RlpError`.
  A fork name given as `bytes` to `seal_hash`, `check_proof_of_work` or `message_id` raises the error class of the method with code 0.
- A Python value of a list or a `dict` with many items no longer overflows the stack when an export reads it as JSON or writes JSON as a Python value ([#1563](https://github.com/ethereum/EthLib/pull/1563)).
  Every export that reads a typed value as JSON, or returns JSON as a typed value, reads and writes the items in a loop.
- The converter of typed values now passes up to 2^22 values in one call, where it passed 1,000,000, so that the longest `ssz_generic` vectors of consensus-spec-tests cross ([#1563](https://github.com/ethereum/EthLib/pull/1563)).
- A chain configuration that the exports read as JSON is now rejected, with code 0, when a fork by block number comes after a fork by timestamp ([#1110](https://github.com/ethereum/EthLib/pull/1110)).
  EIP-6122 requires the forks by timestamp to be scheduled at or after the forks by block.
- leanSPHINCS now hashes with the layout of FIPS 205 ([#1555](https://github.com/ethereum/EthLib/pull/1555)).
  For the same seed and message, `key_gen` and `sign` now return a different key and signature.
  `verify` checks the new layout, so keys and signatures made with 0.3.0 must be made again.
  The sizes are unchanged: a 32-byte seed, a 32-byte public key and a 7740-byte signature.
  The public key is now `PK.seed` then the root, 16 bytes each, in place of the root then the public parameter.
  The Python constant `sphincs.PUBLIC_PARAM_LEN` and the C export `eth_sphincs_const_public_param_len` are removed.
- The gossip topics of Heze are now those of Gloas followed by `inclusion_list` ([#1469](https://github.com/ethereum/EthLib/issues/1469)).
  `consensus.gossip_topics` and `consensus.gossip_topic_bound` now answer at `hegota`, where they raised `ConsensusError`.
  The error of code 304 is gone, since every fork now has a list of topics, and no other error takes that code.
  In Lean, `Config.gossipTopics` returns a `List GossipTopic`, where it returned an `Option`.
- The gossip bounds of four topics are now held to the size limits that the networking specification sets on their messages ([#1610](https://github.com/ethereum/EthLib/issues/1610)).
  `consensus.gossip_topic_bound` answers the limit for `beacon_aggregate_and_proof`, `attester_slashing` and `execution_payload_bid` from `glamsterdam`, and for `inclusion_list` at `hegota`, where it answered the payload cap of 10485760 bytes.
  On mainnet the limits are 16829, 2097616, 196932 and 41112 bytes, and that of a bid is 196934 bytes at `hegota`.
  In Lean, `topicBound_eq` now takes a topic without a size limit, and `decodePayload_message` a message within the size limit of its topic.
- Data column sidecars on gossip and in responses, and inclusion lists in responses, are now held to the size limits of the networking specification ([#1618](https://github.com/ethereum/EthLib/issues/1618)).
  From `glamsterdam`, `consensus.gossip_topic_bound` answers 44072 bytes on mainnet and 18920 on minimal for `data_column_sidecar_{subnet_id}`, where it answered the payload cap of 10485760 bytes.
  `consensus.reqresp_response_bounds` answers (56, 44072) on mainnet and (56, 18920) on minimal for `data_column_sidecars_by_range` and `data_column_sidecars_by_root`, and (152, 41112) for `inclusion_lists_by_indices` at `hegota`.
  Their largest length was the payload cap of 10485760 bytes.
  The limit of a sidecar is its size with a cell and a proof for each blob of the largest blob limit.
  In Lean, `GossipTopic.sizeLimit` now takes the configuration, and the gossip `sizeLimit_ne_none_iff` names the data column sidecar topics.
  From `glamsterdam`, `decodePayload_message` at a sidecar topic now needs a message within the size limit of the topic.
  `responseBounds_eq` now takes a protocol without a size limit, and `decodeResponseChunk_response` a value within the size limit of its protocol.
- The rules that a transaction must pass alone now reject a transaction whose type the fork does not have, with `unsupportedType` and the type ([#1779](https://github.com/ethereum/EthLib/issues/1779)).
  Before, only decoding rejected it, so a block built in Lean could run a type-4 transaction before Pectra, or a type-3 transaction before Dencun.
  `validateTransaction` checks the type first, and the inclusion check and `checkTransaction` call it, so they reject such a transaction too.
  The exports decode each transaction at its fork first, so their answers do not change.
  In Lean, `validateTransaction_eq_ok_iff` ends with the new conjunct `tx.fork ≤ fork`, and `checkInclusion_fork_le` derives it from a passing inclusion check.
  `processTransaction_nonce_lt` no longer takes the hypothesis `tx.fork ≤ fork`.
- `processBlock_split_of` is removed.
  Its reader `processBlock_split` now reads `processBlock_operationsInput` and `OperationsInput.step_of`, and `processBlock_attestationSplit` reads `processBlock_folds`.
  In Lean, a caller that needs a step across the parts of a block before its operations takes the `OperationsInput` that `processBlock_operationsInput` gives.
  It applies `OperationsInput.step_of` to it with the same step arguments.
  The block then continues with `processOperations`, as before.
  No C export or Python function changes.
- A validator write in the epoch laws must keep the slashed flag ([#1421](https://github.com/ethereum/EthLib/issues/1421)).
  No C export or Python function changes.
  In Lean, the `setValidatorAt` field of `EpochFrameLaws` takes a proof of `validator.slashed = old.slashed`, after the proof of the key.
  `EpochFrameLaws.setValidator`, `EpochFrameLaws.setValidator_of_sameBalance` and `EpochFrameLaws.setValidatorAt_of_sameBalance` take the same proof, after the proof of the key.
  A caller passes `rfl` when the write leaves the flag alone, and an instance of the laws takes one more argument.
- The place where a block checks an indexed attestation now also covers the two attestations of an attester slashing ([#1421](https://github.com/ethereum/EthLib/issues/1421)).
  No C export or Python function changes.
  In Lean, `AttestationSite` gains the constructor `slashing`, and a proof that eliminates an `AttestationSite` handles that case too.
  `blockVotes_verified` and `blockStepVotes_verified` keep their statements, so the site that they give may now be either case.
  `AttestationSite.frame` gives the frame from the input of the operations to the state of the check, in both cases.
- The decompositions of a block and of its operations now name the steps after the attestations ([#1421](https://github.com/ethereum/EthLib/issues/1421)).
  No C export or Python function changes.
  In Lean, `processBlock_operationsInput` ends with a new conjunct for the step after the operations.
  From Altair the sync aggregate takes the state after the operations to the state after the block, and before Altair the two are equal.
  A caller that destructures its result adds one pattern at the end.
  The new `processOperations_folds_of` gives the three folds of the operations and a step of any relation across the operations after them.
  `processOperations_folds` is its case for `BlockFrame`, with the same statement.
- An SSZ type path that selects a compatible union option which the union does not declare fails with `badDeclaration` ([#2190](https://github.com/ethereum/EthLib/issues/2190)).
  Before, `Desc.resolveStep` returned the default type, a Boolean, when a union had fewer options than selectors.
  A well-formed union has one option per selector, so its paths resolve as before.
  No C export or Python function changes.
  In Lean, `resolveStep_compatibleUnion` takes the selected child and a proof of `options[slot]? = some child`, and concludes with that child.
  `union_options_share_one_tree` quantifies over that child in the same way.
  `resolveStep_compatibleUnion_of_wellFormed` gives the child for a well-formed union.
- In Lean, the hash of a message to elements of `Fp2` has its count in its type ([#2210](https://github.com/ethereum/EthLib/pull/2210)).
  `hashToFieldFp2` returns `Vector (Fp2 F) count`, where it returned an `Array`, so a caller that needs an array takes `.toArray`.
  The elements, the errors and the points of the hash to `G2` are the same.
  `map_hashToFieldFp2` maps with `Vector.map`, and `hashToFieldFp2_eq_spec` states the same equation over the vector.
  `hashToG2` no longer takes an `Inhabited` instance.
  `map_hashToG2` no longer takes the two instances, or the hypothesis that the map sends the default to the default.
  No C export or Python function changes.
- In Lean, the RLP decoder reads only bytes inside its input ([#2211](https://github.com/ethereum/EthLib/pull/2211)).
  `readPrefix`, `decodeItem`, `decodeItems` and `decodeItemsFrom` take a proof of `stop ≤ input.size`, which `omega` supplies by default.
  `readBigEndian` takes a proof of `pos + k ≤ input.size`.
  The proof helper `readItem` takes the same bound as `decodeItem`, also supplied by `omega` by default.
  `readPrefix_short`, `decodeItemsFrom_eq` and `decodeItems_eq` take the same bound, and `decodeItem_of_readItem` takes it as an implicit argument.
  `decode` keeps its type, the inputs it accepts, its values and its errors.
  No C export or Python function changes.
- In Lean, the reader of an `eth_getProof` answer moves into the specification ([#2099](https://github.com/ethereum/EthLib/issues/2099)).
  `accountProofOfJson`, `storageProofOfJson` and `proofNodes` move from `EthLib.Engine.Exports` to `EthLib.Execution.Rpc`, in `Execution/Rpc/Proof.lean`.
  They keep their types and their errors.
  No C export or Python function changes.
- The chain view serves `eth_getProof`, with the answer that `AccountProof.ofState` builds from the state after the block.

- `eth_config` reports the current, next and last scheduled configurations from Dencun through Glamsterdam.
  As EIP-7910 says, the report leaves out a future fork after Glamsterdam, and `next` and `last` are null when no supported fork remains.
  A fork at a block after genesis is never a next or last configuration.
  In Lean, `ChainView` adds `genesis` and `mergeForkBlock` for the fork checksum.
  Supply both fields in positional constructors, or use structure notation with their `none` defaults.
  `call_unknown` also requires that the method name differ from `eth_config`.
  The configuration given to `rpc_serve` takes the optional keys `mergeForkBlock`, `genesisHash` and `genesisTime`.
  It rejects a malformed value of these keys, one of the genesis pair without the other, and a genesis pair that disagrees with block zero.
  The C and Python function signatures stay the same.

## 0.3.0

Released on 2026-11-06.

0.2.0 had Python bindings for BLS and KZG only.
In 0.3.0, the package `ethlib` has a subpackage for each layer of EthLib:

- `ethlib.cryptography`: `aes`, `bls`, `crc32`, `crc32c`, `ethash`, `hmac`, `kdf`, `keccak`, `kzg`, `secp256k1`, `secp256r1`, `sha256`, `sphincs`, `vrf` and `xmss`
- `ethlib.serialization`: `rlp` and `ssz`
- `ethlib.networking`: `devp2p`, `discv4`, `discv5`, `enr`, `forkid`, `gossip`, `reqresp`, `rlpx`, `snappy` and `varint`
- `ethlib.execution`: `blocks`, `evm`, `fees`, `network`, `pow`, `transactions` and `trie`, with `ethlib.precompiles`, `ethlib.state` and `ethlib.chain`
- `ethlib.consensus` and `ethlib.engine`, for the consensus layer and the Engine API

The sections below list the changes that a caller of 0.2.0, or of master before this release, may need to act on.

### Typed errors in the Python bindings

A failed call into the Python bindings now raises an exception that carries the code and the message of the Lean error ([#310](https://github.com/ethereum/EthLib/pull/310)).
Before, most failures raised a bare `RuntimeError` or `ValueError` with the name of the operation, and the Lean message went to standard error.

The new module `ethlib.errors` defines one exception class for each primitive, such as `KzgError` or `BlsError`.
Each class derives from `EthLibError`, which has two attributes:

- `code`, an integer that names the kind of failure;
- `message`, the text of the Lean error.

Each class also derives from the class that the same failure raised before: `RuntimeError`, `ValueError` or both.
So a caller that catches `RuntimeError` or `ValueError` still catches it.
A caller that parsed the text of an old message must now read `message`.
A message no longer starts with the name of the operation.

The Lean type of each error defines its codes, one for each constructor, from 1.
When one Python class carries several Lean error types, the second type takes its codes from 101, the third from 201, and so on.
A theorem for each error type shows that two errors with one code come from one constructor.

Code 0 means a failure that has no Lean error code.
Examples are an unknown fork name and an input that the export reads before the specification runs.
No Lean error type uses code 0.
Some checks on the type or the length of an argument run in C first, and raise `TypeError` or `ValueError` with no code.

The C signatures of the fallible exports change too.
Each one returns the code and the message of its error, in place of a Lean `IO` error.

### Precompiles

The module `ethlib.precompiles` reaches every precompile by its address, at a fork named by the caller.
`run(fork, address, data, gas)` returns the output, and `price(fork, address, data)` returns the gas that the call charges ([#459](https://github.com/ethereum/EthLib/pull/459)).
A failed call raises `PrecompileError`, whose code names the precompile.

Before the release, master also had the modules `ethlib.precompiles.ecrecover`, `modexp`, `sha256` and `ripemd160`, with the classes `EcrecoverError`, `ModexpError` and `Sha256PrecompileError`.
They are removed, and 0.3.0 does not have them.
A caller of `modexp.modexp(data, gas)` now calls `run(fork, 0x05, data, gas)`, and a caller of `modexp.gas_cost(data)` calls `price(fork, 0x05, data)`.

### Other changes that break callers

- The KZG operations take the trusted setup as an argument and no longer run in `IO` ([#235](https://github.com/ethereum/EthLib/pull/235)), and their byte inputs are typed ([#346](https://github.com/ethereum/EthLib/pull/346)).
- leanXMSS replaced XMSS, with two layers of height 16 ([#134](https://github.com/ethereum/EthLib/pull/134)), and hashes with Keccak-256 in place of BLAKE2s ([#138](https://github.com/ethereum/EthLib/pull/138)).
- The C exports moved into a Lean library of their own, so Lean code that imported them changes its imports ([#119](https://github.com/ethereum/EthLib/pull/119)).
- An integer argument out of its range raises `OverflowError`, as Python's own conversions to a C integer do ([#718](https://github.com/ethereum/EthLib/pull/718)).
  Before, an integer outside [0, 2^64), an EVM opcode above 255 and the range checks of the Python wrappers raised `ValueError`.
  A caller that caught `ValueError` for such an argument now catches `OverflowError`.
- `consensus.verify_data_column_sidecar` takes the signed block before the configuration, in the order of its native export ([#729](https://github.com/ethereum/EthLib/pull/729)).
