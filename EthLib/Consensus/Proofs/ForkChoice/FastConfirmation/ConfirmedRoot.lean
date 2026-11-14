module

public import EthLib.Consensus.Proofs.ForkChoice.AncestorRoots
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic

/-!
# Proofs: how the fast confirmation rule chooses the confirmed block

The rule starts from the block stored before, the finalized block or the observed justified block.

It then stores that block, or a one-confirmed root of the walk from it to the head.

A successful call also passes the checkpoint tests of its walk, and each theorem says which.

No theorem here shows that the confirmed block is safe in an execution or in another store.
-/
@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store : Store preset fork}

/-- The checkpoint tests that a block confirmed after the start passes.

The start is at most one epoch behind the current epoch, or ahead of it.

A root outside the current epoch has a recent voting source, its own or that of the previous head.

When the previous head supplies it, the start is in the epoch before the current one.

That head then also descends from the root.

A root in the current epoch after a start outside it passes the target-justification test.

At a slot that does not start an epoch, the applicable no-conflict test passes.

At such a slot, the applicable unrealized justification is also recent.

These are tests that passed, not proofs of justification or of safety in an execution. -/
def FastConfirmationChecked (store : Store preset fork) (config : Config)
    (fcr : FastConfirmationStore) (head start root : Root) : Prop :=
  ∃ epoch slot rootEpoch startEpoch,
    store.getCurrentStoreEpoch config = .ok epoch ∧ store.getCurrentSlot config = .ok slot ∧
    store.getBlockEpoch root = .ok rootEpoch ∧ store.getBlockEpoch start = .ok startEpoch ∧
    epoch.toNat ≤ startEpoch.toNat + 1 ∧
    ((startEpoch.toNat + 1 = epoch.toNat ∧ rootEpoch ≠ epoch ∧
      (∃ source, store.getVotingSource config fcr.previousSlotHead = .ok source ∧
          epoch.toNat ≤ source.epoch.toNat + 2 ∧
          store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨root, .pending⟩ = .ok true) ∧
      (isStartSlotAtEpoch preset slot = .ok false →
        store.willNoConflictingCheckpointBeJustified config head = .ok true ∧
        ∃ tip justification, (tip = head ∨ tip = fcr.previousSlotHead) ∧
          store.unrealizedJustification tip = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1)) ∨
      ((isStartSlotAtEpoch preset slot = .ok false →
        ∃ justification, store.unrealizedJustification head = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1) ∧
      (rootEpoch = epoch → startEpoch ≠ epoch →
        store.willCurrentTargetBeJustified config head = .ok true) ∧
      (rootEpoch ≠ epoch →
        (∃ source, store.getVotingSource config root = .ok source ∧
          epoch.toNat ≤ source.epoch.toNat + 2) ∧
        (isStartSlotAtEpoch preset slot = .ok false →
          store.willNoConflictingCheckpointBeJustified config head = .ok true))))

/-- The three checks that keep the block stored before as the base of the walk.

The block is at most one epoch behind the current epoch, and the head descends from it.

At the first slot of an epoch, the chain of that block must also still be safe. -/
def KeepsConfirmedRoot (store : Store preset fork) (config : Config)
    (fcr : FastConfirmationStore) (confirmed head : Root) (slot : Slot) : Prop :=
  (∃ epoch blockEpoch, store.getCurrentStoreEpoch config = .ok epoch ∧
      store.getBlockEpoch confirmed = .ok blockEpoch ∧
      epoch.toNat ≤ blockEpoch.toNat + 1) ∧
    store.isAncestor ⟨head, .pending⟩ ⟨confirmed, .pending⟩ = .ok true ∧
    (isStartSlotAtEpoch preset slot = .ok true →
      store.isConfirmedChainSafe config fcr head confirmed = .ok true)

/-- The four checks that replace the base by the observed justified block.

The slot starts an epoch, and the observed block is in the epoch before the current one.

Its checkpoint is the unrealized justification of the head.

The observed block is at a later slot than the base. -/
def ReplacesBase (store : Store preset fork) (config : Config)
    (fcr : FastConfirmationStore) (head base : Root) (slot : Slot) : Prop :=
  isStartSlotAtEpoch preset slot = .ok true ∧
    (∃ observedBlock epoch,
      store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
      store.getCurrentStoreEpoch config = .ok epoch ∧
      Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
    store.unrealizedJustification head = .ok fcr.currentEpochObservedJustifiedCheckpoint ∧
    ∃ baseBlock observedBlock, store.block base = .ok baseBlock ∧
      store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
      baseBlock.slot < observedBlock.slot

/-- The start that the rule selects, with the checks that decide it.

The base is the block stored before when it passes its three checks, else the finalized block.

The start is the observed justified block when the four replacement checks pass, else the base. -/
def SelectsStart (store : Store preset fork) (config : Config)
    (fcr : FastConfirmationStore) (confirmed head : Root) (slot : Slot) (start : Root) : Prop :=
  ∃ base,
    (base = confirmed ∧ store.KeepsConfirmedRoot config fcr confirmed head slot ∨
      base = store.finalizedCheckpoint.root ∧
        ¬store.KeepsConfirmedRoot config fcr confirmed head slot) ∧
    (start = base ∧ ¬store.ReplacesBase config fcr head base slot ∨
      start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧
        store.ReplacesBase config fcr head base slot)

/-- A selected start is the stored block, the finalized block or the observed justified block.

This keeps only some of the checks that decide it. -/
theorem SelectsStart.eq_or {fcr : FastConfirmationStore} {confirmed head start : Root}
    {slot : Slot} (selected : store.SelectsStart config fcr confirmed head slot start) :
    start = confirmed ∧
        store.isAncestor ⟨head, .pending⟩ ⟨confirmed, .pending⟩ = .ok true ∧
        (isStartSlotAtEpoch preset slot = .ok true →
          store.isConfirmedChainSafe config fcr head confirmed = .ok true) ∨
      start = store.finalizedCheckpoint.root ∨
      start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧
        isStartSlotAtEpoch preset slot = .ok true ∧
        (∃ observedBlock epoch,
          store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
          store.getCurrentStoreEpoch config = .ok epoch ∧
          Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
        store.unrealizedJustification head = .ok fcr.currentEpochObservedJustifiedCheckpoint := by
  obtain ⟨base, baseCase, startCase⟩ := selected
  rcases startCase with ⟨rfl, _⟩ | ⟨same, boundary, observed, justified, _⟩
  · rcases baseCase with ⟨same, _, ancestry, safe⟩ | ⟨same, _⟩
    · exact Or.inl ⟨same, ancestry, safe⟩
    · exact Or.inr (Or.inl same)
  · exact Or.inr (Or.inr ⟨same, boundary, observed, justified⟩)

/-- Each root of a walk is in an epoch at or after the epoch of the terminal block. -/
private theorem walk_epoch_le {head start root : Root} {roots : List Root}
    {startEpoch rootEpoch : Epoch}
    (walked : store.getAncestorRoots head start = .ok roots) (member : root ∈ roots)
    (startOk : store.getBlockEpoch start = .ok startEpoch)
    (rootOk : store.getBlockEpoch root = .ok rootEpoch) : startEpoch ≤ rootEpoch := by
  obtain ⟨b, t, bOk, tOk, lt⟩ := slot_lt_of_mem_getAncestorRoots walked (by simp) member
  simp [getBlockEpoch, bOk, tOk, bind, Except.bind, pure, Except.pure] at startOk rootOk
  subst startEpoch
  subst rootEpoch
  exact UInt64.le_iff_toNat_le.mpr (by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp lt)))

/-- A loop over a walk that ends in a later epoch than the start has passed the target test. -/
private theorem target_checked_loop {head start init out : Root} {roots : List Root}
    {body : Root → Root → Except ForkChoiceError (ForInStep Root)}
    (walked : store.getAncestorRoots head start = .ok roots)
    (initial : ∀ se ie, store.getBlockEpoch start = .ok se →
      store.getBlockEpoch init = .ok ie → se ≤ ie ∧
        (se ≠ ie → store.willCurrentTargetBeJustified config head = .ok true))
    (step : ∀ x s r, body x s = .ok r →
      r = .done s ∨ r = .yield x ∧
        ∃ se, store.getBlockEpoch s = .ok se ∧
          ∀ xe, store.getBlockEpoch x = .ok xe →
            (se < xe → store.willCurrentTargetBeJustified config head = .ok true))
    (looped : forIn roots init body = .ok out) :
    ∀ se oe, store.getBlockEpoch start = .ok se → store.getBlockEpoch out = .ok oe →
      se ≤ oe ∧ (se ≠ oe → store.willCurrentTargetBeJustified config head = .ok true) := by
  apply forIn_ok_invariant (fun _ s => ∀ se ie, store.getBlockEpoch start = .ok se →
    store.getBlockEpoch s = .ok ie → se ≤ ie ∧
      (se ≠ ie → store.willCurrentTargetBeJustified config head = .ok true))
    _ initial ?_ ?_ (fun _ h => h) looped
  · intro read x rest s s' split holds stepped
    rcases step x s _ stepped with stopped | ⟨went, ie, oldOk, crossed⟩
    · cases stopped
    obtain rfl := ForInStep.yield.inj went
    intro se xe startOk xOk
    have le := walk_epoch_le walked (split ▸ (by simp)) startOk xOk
    refine ⟨le, ?_⟩
    intro different
    -- A successful step reads the old state epoch before it can yield.
    by_cases checked : store.willCurrentTargetBeJustified config head = .ok true
    · exact checked
    have old := holds se ie startOk oldOk
    have same : se = ie := Classical.byContradiction (fun different => checked (old.2 different))
    subst ie
    exact crossed xe xOk (UInt64.lt_iff_toNat_lt.mpr (by
      have := UInt64.le_iff_toNat_le.mp le
      have := mt UInt64.toNat_inj.mp different
      omega))
  · intro read x rest s s' split holds stepped
    rcases step x s _ stepped with stopped | ⟨went, crossed⟩
    · exact ForInStep.done.inj stopped ▸ holds
    · cases went

/-- The descendant walk returns the start, or a one-confirmed root of the walk to the head.

That root passes the checkpoint tests when the start is at most one epoch behind. -/
private theorem findLatestConfirmedDescendant_walk {fcr : FastConfirmationStore}
    {head start root : Root}
    (found : store.findLatestConfirmedDescendant config fcr head start = .ok root) :
    root = start ∨
      (∃ balanceSource chain later,
        store.checkpointState fcr.currentEpochObservedJustifiedCheckpoint = .ok balanceSource ∧
        store.getAncestorRoots head start = .ok (chain ++ root :: later) ∧
        ∀ member ∈ chain ++ [root], store.isOneConfirmed config head balanceSource
          (store.tallyVotes balanceSource) member = .ok true) ∧
      ((∀ epoch startEpoch, store.getCurrentStoreEpoch config = .ok epoch →
        store.getBlockEpoch start = .ok startEpoch → epoch.toNat ≤ startEpoch.toNat + 1) →
        store.FastConfirmationChecked config fcr head start root) := by
  unfold findLatestConfirmedDescendant at found
  rw [bind_ok_iff] at found
  obtain ⟨epoch, epochOk, found⟩ := found
  rw [bind_ok_iff] at found
  obtain ⟨slot, slotOk, found⟩ := found
  rw [bind_ok_iff] at found
  obtain ⟨atStart, atStartOk, found⟩ := found
  extract_lets arith recentCheck source tally confirmedRoot finish current previous at found
  let good (root : Root) : Prop := ∃ state, source = .ok state ∧
    store.isOneConfirmed config head state (store.tallyVotes state) root = .ok true
  let chainTo (root : Root) : Prop := root = start ∨ ∃ chain later,
    store.getAncestorRoots head start = .ok (chain ++ root :: later) ∧
    ∀ member ∈ chain ++ [root], good member
  suffices result : chainTo root ∧
      ((∀ epoch startEpoch, store.getCurrentStoreEpoch config = .ok epoch →
        store.getBlockEpoch start = .ok startEpoch → epoch.toNat ≤ startEpoch.toNat + 1) →
        root = start ∨ store.FastConfirmationChecked config fcr head start root) by
    rcases result.1 with same | ⟨chain, later, walked, allGood⟩
    · exact Or.inl same
    · by_cases same : root = start
      · exact Or.inl same
      refine Or.inr ⟨?_, fun recent => (result.2 recent).resolve_left same⟩
      obtain ⟨balanceSource, sourced, _⟩ := allGood root (by simp)
      refine ⟨balanceSource, chain, later, sourced, walked, ?_⟩
      intro member isMember
      obtain ⟨other, otherSourced, confirmed⟩ := allGood member isMember
      obtain rfl : balanceSource = other := Except.ok.inj (sourced.symm.trans otherSourced)
      exact confirmed
  have oneStep {x s : Root} {r : ForInStep Root}
      (stepped : (do
        if !(← store.isOneConfirmed config head (← source) (← tally) x) then
          return ForInStep.done s
        return ForInStep.yield x) = .ok r) :
      r = .done s ∨ r = .yield x ∧ good x := by
    simp only [bind_ok_iff] at stepped
    obtain ⟨state, stateOk, votes, votesOk, confirmed, confirmedOk, stepped⟩ := stepped
    change source.map store.tallyVotes = .ok votes at votesOk
    rw [stateOk] at votesOk
    simp only [Except.map, Except.ok.injEq] at votesOk
    subst votes
    cases confirmed <;>
      simp only [Bool.not_false, Bool.not_true, ite_true, Bool.false_eq_true,
        ite_false, pure, Except.pure, Except.ok.injEq] at stepped
    · exact Or.inl stepped.symm
    · exact Or.inr ⟨stepped.symm, state, stateOk, confirmedOk⟩
  have notStart (h : isStartSlotAtEpoch preset slot = .ok false) : atStart = false :=
    Except.ok.inj (atStartOk.symm.trans h)
  have recentNat {e : Epoch} {gap : UInt64}
      (checked : recentCheck e gap = .ok true) : epoch.toNat ≤ e.toNat + gap.toNat := by
    simp only [recentCheck, arith, bind_ok_iff] at checked
    obtain ⟨sum, sumOk, checked⟩ := checked
    have sumValue := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
    have le : epoch ≤ sum := by simpa [pure, Except.pure] using checked.symm
    have := UInt64.le_iff_toNat_le.mp le
    omega
  let previousChecks (mid : Root) : Prop :=
    ∃ se, store.getBlockEpoch start = .ok se ∧
      (mid = start ∨ ∃ me source, store.getBlockEpoch mid = .ok me ∧
        se.toNat + 1 = epoch.toNat ∧ me ≠ epoch ∧
        store.getVotingSource config fcr.previousSlotHead = .ok source ∧
        epoch.toNat ≤ source.epoch.toNat + 2 ∧
        store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨mid, .pending⟩ = .ok true ∧
        (isStartSlotAtEpoch preset slot = .ok false →
          store.willNoConflictingCheckpointBeJustified config head = .ok true ∧
          ∃ tip justification, (tip = head ∨ tip = fcr.previousSlotHead) ∧
            store.unrealizedJustification tip = .ok justification ∧
            epoch.toNat ≤ justification.epoch.toNat + 1))
  -- The gates of the first walk supply checks shared by every root that it accepts.
  have reach : ∃ previousEpochOk se, store.getBlockEpoch start = .ok se ∧
      (previousEpochOk = true →
        se.toNat + 1 = epoch.toNat ∧
        ∃ votingSource, store.getVotingSource config fcr.previousSlotHead = .ok votingSource ∧
          epoch.toNat ≤ votingSource.epoch.toNat + 2 ∧
          (isStartSlotAtEpoch preset slot = .ok false →
            store.willNoConflictingCheckpointBeJustified config head = .ok true ∧
            ∃ tip justification, (tip = head ∨ tip = fcr.previousSlotHead) ∧
              store.unrealizedJustification tip = .ok justification ∧
              epoch.toNat ≤ justification.epoch.toNat + 1)) ∧
      previous previousEpochOk = .ok root := by
    clear_value previous
    simp only [bind_ok_iff] at found
    obtain ⟨se, seOk, sum, sumOk, found⟩ := found
    have sumValue := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
    split at found
    · exact ⟨false, se, seOk, by simp, found⟩
    · rename_i same
      have seValue : se.toNat + 1 = epoch.toNat := by
        have equal : sum = epoch := by simpa using same
        subst sum
        simpa using sumValue.symm
      simp only [bind_ok_iff] at found
      obtain ⟨votingSource, votingOk, sourceRecent, sourceRecentOk, found⟩ := found
      split at found
      · exact ⟨false, se, seOk, by simp, found⟩
      · rename_i sourcePass
        have sourceBound : epoch.toNat ≤ votingSource.epoch.toNat + 2 :=
          recentNat (by have pass : sourceRecent = true := by simpa using sourcePass
                        exact pass ▸ sourceRecentOk)
        split at found
        · rename_i firstSlot
          refine ⟨true, se, seOk, fun _ => ⟨seValue, votingSource, votingOk, sourceBound, ?_⟩,
            found⟩
          intro h
          have := notStart h
          simp_all
        · simp only [bind_ok_iff] at found
          obtain ⟨noConflict, noConflictOk, found⟩ := found
          split at found
          · exact ⟨false, se, seOk, by simp, found⟩
          · rename_i noConflictPass
            have noConflictOk : store.willNoConflictingCheckpointBeJustified config head =
                .ok true := by
              have pass : noConflict = true := by simpa using noConflictPass
              exact pass ▸ noConflictOk
            simp only [bind_ok_iff] at found
            obtain ⟨justification, justificationOk, justificationRecent, justificationRecentOk,
              found⟩ := found
            split at found
            · rename_i justificationPass
              refine ⟨true, se, seOk, fun _ => ⟨seValue, votingSource, votingOk, sourceBound,
                fun _ => ⟨noConflictOk, fcr.previousSlotHead, justification, Or.inr rfl,
                  justificationOk, ?_⟩⟩, found⟩
              exact recentNat (justificationPass ▸ justificationRecentOk)
            · simp only [bind_ok_iff] at found
              obtain ⟨headJustification, headJustificationOk, headRecent, headRecentOk, found⟩ :=
                found
              refine ⟨headRecent, se, seOk, fun passed => ⟨seValue, votingSource, votingOk,
                sourceBound, fun _ => ⟨noConflictOk, head, headJustification, Or.inl rfl,
                  headJustificationOk, ?_⟩⟩, found⟩
              exact recentNat (passed ▸ headRecentOk)
  clear found
  obtain ⟨previousEpochOk, se, seOk, previousOk, found⟩ := reach
  -- Each accepted root adds its own epoch and ancestry checks to those shared checks.
  have first : ∃ mid, previousChecks mid ∧ chainTo mid ∧ current () mid = .ok root := by
    simp only [previous] at found
    split at found
    · rename_i passed
      obtain ⟨seValue, votingSource, votingOk, sourceBound, boundary⟩ := previousOk passed
      rw [bind_ok_iff] at found
      obtain ⟨walk, walked, found⟩ := found
      rw [bind_ok_iff] at found
      obtain ⟨mid, looped, found⟩ := found
      have accepted := forIn_ok_last_kept (kept := fun x => good x ∧ ∃ me,
          store.getBlockEpoch x = .ok me ∧ me ≠ epoch ∧
          store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨x, .pending⟩ = .ok true) (by
        intro x s r stepped
        rw [bind_ok_iff] at stepped
        obtain ⟨me, meOk, stepped⟩ := stepped
        split at stepped
        · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
        · rename_i different
          rw [bind_ok_iff] at stepped
          obtain ⟨onChain, onChainOk, stepped⟩ := stepped
          split at stepped
          · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
          · rename_i onChainPass
            exact (oneStep stepped).imp id (fun h =>
              ⟨h.1, h.2, me, meOk, different, by simp_all⟩)) looped
      rcases accepted with same | ⟨before, after, split, all⟩
      · exact ⟨mid, ⟨se, seOk, Or.inl same⟩, Or.inl same, found⟩
      · obtain ⟨_, me, meOk, different, ancestry⟩ := all mid (by simp)
        exact ⟨mid, ⟨se, seOk, Or.inr ⟨me, votingSource, meOk, seValue, different,
          votingOk, sourceBound, ancestry, boundary⟩⟩,
          Or.inr ⟨before, after, split ▸ walked, fun x hx => (all x hx).1⟩, found⟩
    · exact ⟨start, ⟨se, seOk, Or.inl rfl⟩, Or.inl rfl, found⟩
  clear found
  obtain ⟨mid, firstChecks, firstChain, found⟩ := first
  have firstResult (recent : ∀ epoch startEpoch,
      store.getCurrentStoreEpoch config = .ok epoch →
      store.getBlockEpoch start = .ok startEpoch → epoch.toNat ≤ startEpoch.toNat + 1) :
      mid = start ∨ store.FastConfirmationChecked config fcr head start mid := by
    obtain ⟨se, seOk, same | ⟨me, source, meOk, seValue, different, sourceOk,
      sourceBound, ancestry, boundary⟩⟩ := firstChecks
    · exact Or.inl same
    · exact Or.inr ⟨epoch, slot, me, se, epochOk, slotOk, meOk, seOk,
        recent epoch se epochOk seOk, Or.inl ⟨seValue, different,
          ⟨source, sourceOk, sourceBound, ancestry⟩, boundary⟩⟩
  simp -zeta only [current] at found
  extract_lets tentative currentBody at found
  have reach : ∃ currentEpochOk,
      (currentEpochOk = true → isStartSlotAtEpoch preset slot = .ok false →
        ∃ justification, store.unrealizedJustification head = .ok justification ∧
          epoch.toNat ≤ justification.epoch.toNat + 1) ∧
      currentBody currentEpochOk = .ok root := by
    clear_value currentBody
    split at found
    · rename_i firstSlot
      refine ⟨true, fun _ h => ?_, found⟩
      have := notStart h
      simp_all
    · simp only [bind_ok_iff] at found
      obtain ⟨justification, justificationOk, verdict, verdictOk, found⟩ := found
      exact ⟨verdict, fun h _ => ⟨justification, justificationOk,
        recentNat (h ▸ verdictOk)⟩, found⟩
  clear found
  obtain ⟨currentEpochOk, currentChecks, found⟩ := reach
  simp -zeta only [currentBody] at found
  split at found
  · rename_i passed
    rw [bind_ok_iff] at found
    obtain ⟨walk, walked, found⟩ := found
    rw [bind_ok_iff] at found
    obtain ⟨last, looped, found⟩ := found
    extract_lets tentativeRoot accepted acceptBody at found
    change store.getBlockEpoch last >>= _ = .ok root at found
    rw [bind_ok_iff] at found
    obtain ⟨lastEpoch, lastEpochOk, found⟩ := found
    -- Rejection restores the first walk's result, not the tentative result of the second walk.
    have acceptedResult : root = mid ∨ root = last ∧
        (lastEpoch ≠ epoch →
          (∃ source, store.getVotingSource config last = .ok source ∧
            epoch.toNat ≤ source.epoch.toNat + 2) ∧
          (isStartSlotAtEpoch preset slot = .ok false →
            store.willNoConflictingCheckpointBeJustified config head = .ok true)) := by
      have finishResult {accept : Bool} (ended : acceptBody accept = .ok root) :
          (accept = true ∧ root = last) ∨ (accept = false ∧ root = mid) := by
        simp only [acceptBody, finish] at ended
        split at ended
        · exact Or.inl ⟨by assumption, by simpa [pure, Except.pure, tentativeRoot, accepted]
            using ended.symm⟩
        · rename_i notAccepted
          have rejected : accept = false := Bool.eq_false_iff.mpr notAccepted
          exact Or.inr ⟨rejected, by simpa [pure, Except.pure] using ended.symm⟩
      split at found
      · rename_i isCurrent
        simp only [pure, Except.pure, bind, Except.bind] at found
        rcases finishResult (accept := true) found with ⟨_, same⟩ | ⟨bad, _⟩
        · exact Or.inr ⟨same, fun h => False.elim (h isCurrent)⟩
        · cases bad
      · rw [bind_ok_iff] at found
        obtain ⟨votingSource, votingOk, found⟩ := found
        rw [bind_ok_iff] at found
        obtain ⟨sourceRecent, sourceRecentOk, found⟩ := found
        split at found
        · simp only [pure, Except.pure, bind, Except.bind] at found
          rcases finishResult (accept := false) found with ⟨bad, _⟩ | ⟨_, same⟩
          · cases bad
          · exact Or.inl same
        · rename_i recentPass
          have pass : sourceRecent = true := by simpa using recentPass
          have bound := recentNat (pass ▸ sourceRecentOk)
          split at found
          · rename_i firstSlot
            simp only [pure, Except.pure, bind, Except.bind] at found
            rcases finishResult (accept := true) found with ⟨_, same⟩ | ⟨bad, _⟩
            · refine Or.inr ⟨same, fun _ => ⟨⟨votingSource, votingOk, bound⟩, ?_⟩⟩
              intro h
              have := notStart h
              simp_all
            · cases bad
          · rw [bind_ok_iff] at found
            obtain ⟨accept, acceptOk, found⟩ := found
            rcases finishResult found with ⟨rfl, same⟩ | ⟨_, same⟩
            · exact Or.inr ⟨same, fun _ => ⟨⟨votingSource, votingOk, bound⟩,
                fun _ => acceptOk⟩⟩
            · exact Or.inl same
    have step : ∀ x s r, (do
        if (← store.getBlockEpoch x) > (← store.getBlockEpoch s) then
          if !(← store.willCurrentTargetBeJustified config head) then
            return ForInStep.done s
        if !(← store.isOneConfirmed config head (← source) (← tally) x) then
          return ForInStep.done s
        return ForInStep.yield x) = .ok r →
        r = ForInStep.done s ∨ r = .yield x ∧ good x ∧
          ∃ se, store.getBlockEpoch s = .ok se ∧
            ∀ xe, store.getBlockEpoch x = .ok xe →
              (se < xe → store.willCurrentTargetBeJustified config head = .ok true) := by
        intro x s r stepped
        simp only [bind_ok_iff] at stepped
        obtain ⟨xe, xeOk, se, oldOk, stepped⟩ := stepped
        split at stepped
        · rename_i crosses
          rw [bind_ok_iff] at stepped
          obtain ⟨check, checkOk, stepped⟩ := stepped
          split at stepped
          · exact Or.inl (by simpa [pure, Except.pure] using stepped.symm)
          · rename_i checkPass
            exact (oneStep stepped).imp id (fun h =>
              ⟨h.1, h.2, se, oldOk, fun _ _ _ => by simp_all⟩)
        · rename_i noCross
          refine (oneStep stepped).imp id (fun h => ⟨h.1, h.2, se, oldOk, ?_⟩)
          intro other otherOk lt
          obtain rfl : xe = other := Except.ok.inj (xeOk.symm.trans otherOk)
          exact absurd lt noCross
    have second := forIn_ok_last_kept (kept := good) (fun x s r h =>
      (step x s r h).imp id (fun h => ⟨h.1, h.2.1⟩)) looped
    have target := target_checked_loop (config := config) walked (by
      intro me ie meOk ieOk
      have same : me = ie := Except.ok.inj (meOk.symm.trans ieOk)
      subst ie
      exact ⟨UInt64.le_refl _, by simp⟩) (fun x s r h =>
        (step x s r h).imp id (fun h => ⟨h.1, h.2.2⟩)) looped
    rcases acceptedResult with rfl | ⟨rfl, acceptedChecks⟩
    · exact ⟨firstChain, firstResult⟩
    · refine ⟨?_, ?_⟩
      · rcases second with same | ⟨chain, later, split, allGood⟩
        · exact same ▸ firstChain
        · subst split
          rcases firstChain with rfl | ⟨earlier, between, firstWalked, earlierGood⟩
          · exact Or.inr ⟨chain, later, walked, allGood⟩
          · have rest := getAncestorRoots_of_append firstWalked
            obtain rfl : between = chain ++ root :: later :=
              Except.ok.inj (rest.symm.trans walked)
            refine Or.inr ⟨earlier ++ mid :: chain, later, by simpa using firstWalked, ?_⟩
            intro member isMember
            rw [show earlier ++ mid :: chain ++ [root] =
              (earlier ++ [mid]) ++ (chain ++ [root]) by simp] at isMember
            exact (List.mem_append.mp isMember).elim (earlierGood member) (allGood member)
      · intro recent
        obtain ⟨se, seOk, firstCases⟩ := firstChecks
        have startToMid : ∃ me, store.getBlockEpoch mid = .ok me := by
          rcases firstCases with rfl | ⟨me, source, meOk, rest⟩
          · exact ⟨se, seOk⟩
          · exact ⟨me, meOk⟩
        obtain ⟨me, meOk⟩ := startToMid
        have lastTarget := target me lastEpoch meOk lastEpochOk
        refine Or.inr ⟨epoch, slot, lastEpoch, se, epochOk, slotOk, lastEpochOk, seOk,
          recent epoch se epochOk seOk, Or.inr ⟨currentChecks passed, ?_, acceptedChecks⟩⟩
        intro lastCurrent startDifferent
        have midDifferent : me ≠ lastEpoch := by
          intro same
          subst me
          rcases firstCases with same | ⟨_, _, midOk, seValue, midNotCurrent, _⟩
          · subst mid
            have := Except.ok.inj (seOk.symm.trans meOk)
            exact startDifferent (this.trans lastCurrent)
          · have := Except.ok.inj (midOk.symm.trans meOk)
            exact midNotCurrent (this.trans lastCurrent)
        exact lastTarget.2 midDifferent
  · have same : root = mid := by simpa [finish, pure, Except.pure] using found.symm
    exact same ▸ ⟨firstChain, firstResult⟩

/-- The descendant search returns the start, or a root that passes the checkpoint tests.

It assumes the start is at most one epoch behind, as the caller checks before the search. -/
theorem findLatestConfirmedDescendant_checked {fcr : FastConfirmationStore}
    {head start root : Root}
    (recent : ∀ epoch startEpoch, store.getCurrentStoreEpoch config = .ok epoch →
      store.getBlockEpoch start = .ok startEpoch → epoch.toNat ≤ startEpoch.toNat + 1)
    (found : store.findLatestConfirmedDescendant config fcr head start = .ok root) :
    root = start ∨ store.FastConfirmationChecked config fcr head start root := by
  exact (findLatestConfirmedDescendant_walk found).imp id (fun h => h.2 recent)

/-- The latest confirmed descendant is the start, or a one-confirmed root of the walk to the head.

Each root of the walk before it is one-confirmed too.

The walk goes from the head back to the start, without the start, with the oldest root first.

The votes are those of the state of the observed justified checkpoint.

The theorem does not record the other checks of the two walks of the rule.

It leaves out the checks on the epochs of the start and of the walked blocks.

It also leaves out the check on the head of the slot before.

It also leaves out the checks that a voting source or an unrealized justification is recent.

It also leaves out the two checks on the justification of the target of the current epoch. -/
theorem findLatestConfirmedDescendant_eq_or {fcr : FastConfirmationStore}
    {head start root : Root}
    (found : store.findLatestConfirmedDescendant config fcr head start = .ok root) :
    root = start ∨ ∃ balanceSource chain later,
      store.checkpointState fcr.currentEpochObservedJustifiedCheckpoint = .ok balanceSource ∧
      store.getAncestorRoots head start = .ok (chain ++ root :: later) ∧
      ∀ member ∈ chain ++ [root], store.isOneConfirmed config head balanceSource
        (store.tallyVotes balanceSource) member = .ok true := by
  exact (findLatestConfirmedDescendant_walk found).imp id And.left

/-- The latest confirmed block comes from a start that passed the checks deciding it.

It is that start, or a later one-confirmed root of the walk that passes the checkpoint tests. -/
private theorem getLatestConfirmed_walk {fcr : FastConfirmationStore} {head root : Root}
    (latest : store.getLatestConfirmed config fcr head = .ok root) :
    ∃ slot start, store.getCurrentSlot config = .ok slot ∧
      store.SelectsStart config fcr fcr.confirmedRoot head slot start ∧
      (root = start ∨ store.FastConfirmationChecked config fcr head start root ∧
        store.findLatestConfirmedDescendant config fcr head start = .ok root ∧
        ∃ balanceSource chain later,
          store.checkpointState fcr.currentEpochObservedJustifiedCheckpoint = .ok balanceSource ∧
          store.getAncestorRoots head start = .ok (chain ++ root :: later) ∧
          ∀ member ∈ chain ++ [root], store.isOneConfirmed config head balanceSource
            (store.tallyVotes balanceSource) member = .ok true) := by
  unfold getLatestConfirmed at latest
  rw [bind_ok_iff] at latest
  obtain ⟨currentEpoch, epochFound, latest⟩ := latest
  rw [bind_ok_iff] at latest
  obtain ⟨slot, slotFound, latest⟩ := latest
  refine ⟨slot, ?_⟩
  extract_lets arith confirmedRoot observed finish observedRoot afterReset finalizedRoot
    resetBody at latest
  let kept : Prop := store.KeepsConfirmedRoot config fcr fcr.confirmedRoot head slot
  -- Keep the reset decision paired with the continuation that consumes it.
  have reset : ∃ reset, (reset = false → kept) ∧ (reset = true → ¬kept) ∧
      resetBody reset = .ok root := by
    clear_value resetBody
    rw [bind_ok_iff] at latest
    obtain ⟨blockEpoch, blockEpochOk, latest⟩ := latest
    rw [bind_ok_iff] at latest
    obtain ⟨sum, sumOk, latest⟩ := latest
    have sumValue := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
    simp only [UInt64.toNat_one] at sumValue
    -- The epoch check for keeping the stored block is the negation of the staleness test.
    have epochCheck : (∃ epoch be, store.getCurrentStoreEpoch config = .ok epoch ∧
        store.getBlockEpoch fcr.confirmedRoot = .ok be ∧ epoch.toNat ≤ be.toNat + 1) ↔
        ¬sum < currentEpoch := by
      constructor
      · rintro ⟨epoch, be, epochOk, beOk, le⟩ stale
        obtain rfl : currentEpoch = epoch := Except.ok.inj (epochFound.symm.trans epochOk)
        obtain rfl : blockEpoch = be := Except.ok.inj (blockEpochOk.symm.trans beOk)
        have := UInt64.lt_iff_toNat_lt.mp stale
        omega
      · intro fresh
        have := UInt64.not_lt.mp fresh
        refine ⟨currentEpoch, blockEpoch, epochFound, blockEpochOk, ?_⟩
        have := UInt64.le_iff_toNat_le.mp this
        omega
    split at latest
    · rename_i stale
      exact ⟨true, by simp, fun _ held => epochCheck.mp held.1 stale, latest⟩
    · rename_i fresh
      rw [bind_ok_iff] at latest
      obtain ⟨onChain, ancestry, latest⟩ := latest
      split at latest
      · rename_i offChain
        refine ⟨true, by simp, fun _ held => ?_, latest⟩
        have same := Except.ok.inj (ancestry.symm.trans held.2.1)
        simp [same] at offChain
      · rename_i isOnChain
        obtain rfl : onChain = true := by simpa using isOnChain
        rw [bind_ok_iff] at latest
        obtain ⟨atStart, startChecked, latest⟩ := latest
        split at latest
        · rename_i startTrue
          obtain rfl : atStart = true := by simpa using startTrue
          rw [bind_ok_iff] at latest
          obtain ⟨safe, chainChecked, latest⟩ := latest
          refine ⟨!safe, fun notReset => ⟨epochCheck.mpr fresh, ancestry, fun _ => ?_⟩,
            fun isReset held => ?_, latest⟩
          · obtain rfl : safe = true := by simpa using notReset
            exact chainChecked
          · have same := Except.ok.inj (chainChecked.symm.trans (held.2.2 startChecked))
            simp [same] at isReset
        · rename_i notStart
          refine ⟨false, fun _ => ⟨epochCheck.mpr fresh, ancestry, fun isStart => ?_⟩,
            by simp, latest⟩
          exact absurd (Except.ok.inj (startChecked.symm.trans isStart)) (by simpa using notStart)
  clear latest
  obtain ⟨reset, keeps, drops, latest⟩ := reset
  have base : ∃ base, (base = fcr.confirmedRoot ∧ kept ∨
      base = store.finalizedCheckpoint.root ∧ ¬kept) ∧ afterReset () base = .ok root := by
    cases reset
    · exact ⟨fcr.confirmedRoot, Or.inl ⟨rfl, keeps rfl⟩, latest⟩
    · exact ⟨store.finalizedCheckpoint.root, Or.inr ⟨rfl, drops rfl⟩, latest⟩
  clear latest keeps drops
  obtain ⟨base, baseCase, latest⟩ := base
  let over : Prop := store.ReplacesBase config fcr head base slot
  have start : ∃ start, (start = base ∧ ¬over ∨
      start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧ over) ∧
      finish () start = .ok root := by
    clear_value finish
    simp only [afterReset, bind_ok_iff] at latest
    obtain ⟨atStart, startChecked, observedBlock, observedFound, observedEpoch, epochAdded,
      justified, justification, baseBlock, baseFound, latest⟩ := latest
    split at latest
    · rename_i replaced
      refine ⟨observedRoot, Or.inr ⟨rfl, replaced.1 ▸ startChecked,
        ⟨observedBlock, currentEpoch, observedFound, epochFound,
          replaced.2.1 ▸ mapError_ok_iff.mp epochAdded⟩,
        justification.trans (congrArg Except.ok replaced.2.2.1.symm),
        baseBlock, observedBlock, baseFound, observedFound, replaced.2.2.2⟩, latest⟩
    · rename_i kept'
      refine ⟨base, Or.inl ⟨rfl, ?_⟩, latest⟩
      rintro ⟨isStart, ⟨ob, epoch, obFound, epochOk, added⟩, headJustified, bb, ob', bbFound,
        ob'Found, lower'⟩
      apply kept'
      obtain rfl : atStart = true := Except.ok.inj (startChecked.symm.trans isStart)
      obtain rfl : ob = observedBlock := Except.ok.inj (obFound.symm.trans observedFound)
      obtain rfl : ob' = ob := Except.ok.inj (ob'Found.symm.trans obFound)
      obtain rfl : bb = baseBlock := Except.ok.inj (bbFound.symm.trans baseFound)
      obtain rfl : epoch = currentEpoch := Except.ok.inj (epochOk.symm.trans epochFound)
      have sameEpoch : observedEpoch = epoch :=
        Except.ok.inj ((mapError_ok_iff.mp epochAdded).symm.trans added)
      have sameJustified : justified = fcr.currentEpochObservedJustifiedCheckpoint :=
        Except.ok.inj (justification.symm.trans headJustified)
      exact ⟨rfl, sameEpoch, sameJustified.symm, lower'⟩
  clear latest
  obtain ⟨start, startCase, latest⟩ := start
  refine ⟨start, slotFound, ⟨base, baseCase, startCase⟩, ?_⟩
  simp only [finish, bind_ok_iff] at latest
  obtain ⟨startEpoch, startOk, sum, sumOk, latest⟩ := latest
  split at latest
  · rename_i recentStart
    have recent : ∀ epoch se, store.getCurrentStoreEpoch config = .ok epoch →
        store.getBlockEpoch start = .ok se → epoch.toNat ≤ se.toNat + 1 := by
      intro epoch se epochOk seOk
      obtain rfl : currentEpoch = epoch := Except.ok.inj (epochFound.symm.trans epochOk)
      obtain rfl : startEpoch = se := Except.ok.inj (startOk.symm.trans seOk)
      have value := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp sumOk)).2
      have le := UInt64.le_iff_toNat_le.mp recentStart
      simp only [UInt64.toNat_one] at value
      omega
    rcases findLatestConfirmedDescendant_walk latest with same | ⟨chain, checked⟩
    · exact Or.inl same
    · exact Or.inr ⟨checked recent, latest, chain⟩
  · exact Or.inl (Except.ok.inj latest).symm

/-- The latest confirmed block comes from a start that passed the checks deciding it.

It is that start, or a block found from it that passes the checkpoint tests. -/
theorem getLatestConfirmed_checked_start {fcr : FastConfirmationStore} {head root : Root}
    (latest : store.getLatestConfirmed config fcr head = .ok root) :
    ∃ slot start, store.getCurrentSlot config = .ok slot ∧
      store.SelectsStart config fcr fcr.confirmedRoot head slot start ∧
      (root = start ∨ store.FastConfirmationChecked config fcr head start root ∧
        store.findLatestConfirmedDescendant config fcr head start = .ok root) := by
  obtain ⟨slot, start, slotOk, startCase, result⟩ := getLatestConfirmed_walk latest
  exact ⟨slot, start, slotOk, startCase,
    result.imp id (fun h => ⟨h.1, h.2.1⟩)⟩

/-- The latest confirmed block is a block to start from, or its latest confirmed descendant.

The rule starts from the stored block, the finalized block or the observed justified block.

It keeps the stored block only when that block is in the chain of the head.

At the first slot of an epoch, the chain of the stored block must also still be safe.

It takes the observed justified block only at the first slot of an epoch.

That block is then in the epoch before the current one.

Its checkpoint is then the unrealized justification of the head.

The theorem does not record the other checks on the epochs and the slots of the blocks. -/
theorem getLatestConfirmed_eq_or {fcr : FastConfirmationStore} {head root : Root}
    (latest : store.getLatestConfirmed config fcr head = .ok root) :
    ∃ slot start, store.getCurrentSlot config = .ok slot ∧
      (start = fcr.confirmedRoot ∧
          store.isAncestor ⟨head, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
          (isStartSlotAtEpoch preset slot = .ok true →
            store.isConfirmedChainSafe config fcr head fcr.confirmedRoot = .ok true) ∨
        start = store.finalizedCheckpoint.root ∨
        start = fcr.currentEpochObservedJustifiedCheckpoint.root ∧
          isStartSlotAtEpoch preset slot = .ok true ∧
          (∃ observedBlock epoch,
            store.block fcr.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
            store.getCurrentStoreEpoch config = .ok epoch ∧
            Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
          store.unrealizedJustification head =
            .ok fcr.currentEpochObservedJustifiedCheckpoint) ∧
      (root = start ∨ store.findLatestConfirmedDescendant config fcr head start = .ok root) := by
  obtain ⟨slot, start, slotOk, startCase, result⟩ := getLatestConfirmed_walk latest
  exact ⟨slot, start, slotOk, startCase.eq_or, result.imp id (fun h => h.2.1)⟩

/-- The fast confirmation of a slot stores its selected start, or a later root of its walk.

That root and each root before it in the walk are one-confirmed.

It also passes the checkpoint tests of its walk, read in the fast confirmation store after the call.

The theorem assumes only that the call succeeds, and it says nothing about safety. -/
theorem onFastConfirmation_checked {fcr after : FastConfirmationStore}
    (confirmed : store.onFastConfirmation config fcr = .ok after) :
    ∃ head slot start, store.getHead config = .ok head ∧
      store.getCurrentSlot config = .ok slot ∧
      store.SelectsStart config after fcr.confirmedRoot head.root slot start ∧
      (after.confirmedRoot = start ∨
        after.confirmedRoot ≠ start ∧
        store.FastConfirmationChecked config after head.root start after.confirmedRoot ∧
        ∃ balanceSource chain later,
          store.checkpointState after.currentEpochObservedJustifiedCheckpoint =
            .ok balanceSource ∧
          store.getAncestorRoots head.root start = .ok (chain ++ after.confirmedRoot :: later) ∧
          ∀ member ∈ chain ++ [after.confirmedRoot], store.isOneConfirmed config head.root
            balanceSource (store.tallyVotes balanceSource) member = .ok true) := by
  unfold onFastConfirmation at confirmed
  simp only [bind_ok_iff] at confirmed
  obtain ⟨head, headOk, updated, updateOk, root, latest, confirmed⟩ := confirmed
  simp only [pure, Except.pure, Except.ok.injEq] at confirmed
  subst confirmed
  obtain ⟨slot, start, slotOk, startCase, result⟩ :=
    getLatestConfirmed_walk latest
  rw [updateFastConfirmationVariables_confirmedRoot updateOk] at startCase
  refine ⟨head, slot, start, headOk, slotOk, startCase, ?_⟩
  rcases result with same | ⟨checked, _, walk⟩
  · exact Or.inl same
  · obtain ⟨balanceSource, chain, later, sourceOk, walked, confirmedAll⟩ := walk
    refine Or.inr ⟨fun same => ?_, checked, balanceSource, chain, later, sourceOk, walked,
      confirmedAll⟩
    obtain ⟨b, t, bOk, tOk, lt⟩ := slot_lt_of_mem_getAncestorRoots walked (by simp)
      (List.mem_append_right _ (List.mem_cons_self ..))
    rw [← same] at tOk
    obtain rfl : b = t := Except.ok.inj (bOk.symm.trans tOk)
    exact UInt64.lt_irrefl _ lt

/-- The fast confirmation of a slot stores a block to start from, or a confirmed block after it.

The rule starts from the block stored before, the finalized block or the observed justified block.

It keeps the block stored before only when that block is in the chain of the head of the store.

At the first slot of an epoch, the chain of that block must also still be safe.

It takes the observed justified block only at the first slot of an epoch.

That block is then in the epoch before the current one.

Its checkpoint is then the unrealized justification of the head.

A later block is a root of the walk from the start to the head.

That block and each root before it in the walk are one-confirmed.

The observed justified checkpoint is that of the store after the call, as the rule reads it.

The theorem does not record the other checks of the rule. -/
theorem onFastConfirmation_confirmedRoot {fcr after : FastConfirmationStore}
    (confirmed : store.onFastConfirmation config fcr = .ok after) :
    ∃ head slot start, store.getHead config = .ok head ∧
      store.getCurrentSlot config = .ok slot ∧
      (start = fcr.confirmedRoot ∧
          store.isAncestor ⟨head.root, .pending⟩ ⟨fcr.confirmedRoot, .pending⟩ = .ok true ∧
          (isStartSlotAtEpoch preset slot = .ok true →
            store.isConfirmedChainSafe config after head.root fcr.confirmedRoot = .ok true) ∨
        start = store.finalizedCheckpoint.root ∨
        start = after.currentEpochObservedJustifiedCheckpoint.root ∧
          isStartSlotAtEpoch preset slot = .ok true ∧
          (∃ observedBlock epoch,
            store.block after.currentEpochObservedJustifiedCheckpoint.root = .ok observedBlock ∧
            store.getCurrentStoreEpoch config = .ok epoch ∧
            Uint64.addChecked (computeEpochAtSlot preset observedBlock.slot) 1 = .ok epoch) ∧
          store.unrealizedJustification head.root =
            .ok after.currentEpochObservedJustifiedCheckpoint) ∧
      (after.confirmedRoot = start ∨ ∃ balanceSource chain later,
        store.checkpointState after.currentEpochObservedJustifiedCheckpoint = .ok balanceSource ∧
        store.getAncestorRoots head.root start = .ok (chain ++ after.confirmedRoot :: later) ∧
        ∀ member ∈ chain ++ [after.confirmedRoot], store.isOneConfirmed config head.root
          balanceSource (store.tallyVotes balanceSource) member = .ok true) := by
  obtain ⟨head, slot, start, headOk, slotOk, startCase, result⟩ :=
    onFastConfirmation_checked confirmed
  exact ⟨head, slot, start, headOk, slotOk, startCase.eq_or, result.imp id (fun h => h.2.2)⟩

end Store

end EthLib.Consensus
