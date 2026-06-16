universe uα

def idxIter {α : Type uα}
    (f : Nat → α → α)
    (start steps : Nat)
    (x : α) : α :=
  match steps with
  | 0 => x
  | n + 1 => f (start + n) (idxIter f start n x)

@[simp]
theorem idxIter_zero {α : Type uα}
    (f : Nat → α → α)
    (start : Nat)
    (x : α) :
    idxIter f start 0 x = x :=
  by rfl

@[simp]
theorem idxIter_succ {α : Type uα}
    (f : Nat → α → α)
    (start i : Nat)
    (x : α) :
    idxIter f start (i + 1) x = f (start + i) (idxIter f start i x) :=
  by rfl

theorem idxIter_comp {α : Type uα}
    (f : Nat → α → α)
    (start i j : Nat)
    (x : α) :
    idxIter f start (i + j) x
    =
    idxIter f (start + i) j (idxIter f start i x) :=
  by
    induction j with
    | zero =>
        simp [idxIter]
    | succ j ih =>
        simp [idxIter, ih, Nat.add_assoc]


abbrev TweakableHash (PP TW X Y : Type) :=
  PP → TW → X → Y

namespace TweakableHash

def chain {PP TW X Y : Type}
    (thf : TweakableHash PP TW X Y)
    (outToIn : Y → X)
    (twat : Nat → TW)
    (pp : PP)
    (start steps : Nat)
    (x : Y) : Y :=
  idxIter
    (fun pos y => thf pp (twat pos) (outToIn y))
    start
    steps
    x

@[simp]
theorem chain_zero {PP TW X Y: Type}
    (thf : TweakableHash PP TW X Y)
    (outToIn : Y → X)
    (twat : Nat → TW)
    (pp : PP)
    (start : Nat)
    (x : Y) :
    chain thf outToIn twat pp start 0 x = x :=
  by rfl

@[simp]
theorem chain_succ {PP TW X Y: Type}
    (thf : TweakableHash PP TW X Y)
    (outToIn : Y → X)
    (twat : Nat → TW)
    (pp : PP)
    (start i : Nat)
    (x : Y) :
    chain thf outToIn twat pp start (i + 1) x
    =
    thf pp (twat (start + i)) (outToIn (chain thf outToIn twat pp start i x)) :=
  by rfl

theorem chain_comp {PP TW X Y: Type}
    (thf : TweakableHash PP TW X Y)
    (outToIn : Y → X)
    (twat : Nat → TW)
    (pp : PP)
    (start i j : Nat)
    (x : Y) :
    chain thf outToIn twat pp start (i + j) x
    =
    chain thf outToIn twat pp (start + i) j (chain thf outToIn twat pp start i x) :=
  by
    simp [chain, idxIter_comp]

def isColl {PP TW X Y: Type}
    (thf : TweakableHash PP TW X Y)
    (pp : PP)
    (tw : TW)
    (x x' : X) : Prop :=
  x ≠ x' ∧ thf pp tw x = thf pp tw x'

theorem chain_coll {PP TW X Y: Type}
    (thf : TweakableHash PP TW X Y)
    (outToIn : Y → X)
    (twat : Nat → TW)
    (pp : PP)
    (start steps : Nat)
    (x x' : Y)
    (outToIn_inj : Function.Injective outToIn)
    (xxp_neq : x ≠ x'):
    chain thf outToIn twat pp start steps x = chain thf outToIn twat pp start steps x' →
    ∃i : Nat, i < steps ∧ isColl thf pp (twat (start + i)) (outToIn (chain thf outToIn twat pp start i x)) (outToIn (chain thf outToIn twat pp start i x')) :=
  by
    induction steps with
    | zero =>
        simp only [chain_zero]
        intro heq
        contradiction
    | succ steps ih =>
        intro heqnext
        by_cases hprev :
          chain thf outToIn twat pp start steps x = chain thf outToIn twat pp start steps x'
        · obtain ⟨i, hi, hcoll⟩ := ih hprev
          refine ⟨i, ?_, hcoll⟩
          exact Nat.lt_trans hi (Nat.lt_succ_self steps)
        · refine ⟨steps, (Nat.lt_succ_self steps), ?_⟩
          constructor
          · intro heqout
            apply hprev
            exact outToIn_inj heqout
          · simpa only [chain_succ] using heqnext
end TweakableHash
