universe u

inductive HashTree (H : Type u) where
  | leaf (value : H)
  | node (value : H) (left right : HashTree H)

namespace HashTree

variable {H : Type u}

def value : HashTree H → H
  | .leaf value => value
  | .node value _ _ => value

def height : HashTree H → Nat
  | .leaf _ => 0
  | .node _ l r => 1 + max (height l) (height r)

def numLeaves : HashTree H → Nat
  | .leaf _ => 1
  | .node _ l r => l.numLeaves + r.numLeaves



def IsPerfect : HashTree H → Prop
  | .leaf _ => True
  | .node _ l r => l.height = r.height ∧ l.IsPerfect ∧ r.IsPerfect

def IsBalanced : HashTree H → Prop
  | .leaf _ => True
  | .node _ l r => (l.height - r.height) + (r.height - l.height) ≤ 1

def IsPerfectlyBalanced : HashTree H → Prop
  | .leaf _ => True
  | .node _ l r => l.height = r.height


private def incLevel
    (f : H → H → H) :
    List (HashTree H) → List (HashTree H)
  | [] => []
  | [tree] => [tree]
  | l :: r :: trees => (node (f l.value r.value) l r) :: incLevel f trees

private theorem incLevel_length_le
    (f : H → H → H)
    (trees : List (HashTree H)) :
    (incLevel f trees).length ≤ trees.length :=
  match trees with
  | [] => by
      simp [incLevel]
  | [tree] => by
      simp [incLevel]
  | l :: r :: trees => by
      simp only [incLevel, List.length_cons]
      have := incLevel_length_le f trees
      omega

private theorem incLevel_length_lt
    (f : H → H → H)
    (l r : HashTree H)
    (trees : List (HashTree H)) :
    (incLevel f (l :: r :: trees)).length < (l :: r :: trees).length :=
  by
    simp [incLevel]
    have := (incLevel_length_le f trees)
    omega

private theorem incLevel_length_ge1
    (f : H → H → H)
    (l r : HashTree H)
    (trees : List (HashTree H)) :
    1 ≤ (incLevel f (l :: r :: trees)).length :=
  by
    simp [incLevel]

private def fromTreesO
    (f : H → H → H) :
    List (HashTree H) → Option (HashTree H)
  | [] => none
  | [tree] => some tree
  | l :: r :: trees =>
      fromTreesO f (incLevel f (l :: r :: trees))
termination_by trees => trees.length
decreasing_by
  exact incLevel_length_lt f l r trees

private theorem fromTreesO_exists
    (f : H → H → H)
    (trees : List (HashTree H)) :
    trees ≠ [] →
      ∃ tree, fromTreesO f trees = some tree :=
  match trees with
  | [] => by
      intro f
      contradiction
  | [tree] => by
      simp [fromTreesO]
  | l :: r :: trees => by
      intro _
      rw [fromTreesO]
      exact fromTreesO_exists f
            (incLevel f (l :: r :: trees))
            (by simp [incLevel])
termination_by trees.length
decreasing_by
  exact incLevel_length_lt f l r trees

private theorem fromTreesO_isSome
    (f : H → H → H)
    (trees : List (HashTree H)) :
    trees ≠ [] →
      (fromTreesO f trees).isSome :=
  by
    rw [Option.isSome_iff_exists]
    apply fromTreesO_exists f trees

def fromTrees
    (f : H → H → H)
    (trees : List (HashTree H))
    (trees_nonnil : trees ≠ []) : HashTree H :=
  (fromTreesO f trees).get (fromTreesO_isSome f trees trees_nonnil)

private def fromTreesDivO
    (f : H → H → H) :
    List (HashTree H) → Option (HashTree H)
  | [] =>
      none
  | [tree] =>
      some tree
  | a :: b :: rest =>
      let trees := a :: b :: rest
      let k := trees.length / 2

      do
        let l ← fromTreesDivO f (trees.take k)
        let r ← fromTreesDivO f (trees.drop k)
        return node (f l.value r.value) l r
termination_by trees => trees.length
decreasing_by
  all_goals
    simp
    omega


private theorem fromTreesDivO_exists_pow2
    (f : H → H → H)
    (trees : List (HashTree H))
    (h : Nat) :
    trees.length = 2 ^ h →
      ∃ tree, (fromTreesDivO f trees) = some tree :=
  match trees with
  | [] => by
      grind
  | [tree] => by
      intro _
      exact ⟨tree, by simp [fromTreesDivO]⟩
  | a :: b :: rest => by
      intro hlen
      cases h with
      | zero =>
           simp at hlen
      | succ h =>
          let trees := a :: b :: rest
          let k := trees.length / 2

          have htrees : trees.length = 2 ^ (h + 1) := by
            simpa [trees] using hlen
          have hk : k = 2 ^ h := by
            dsimp [k]
            rw [htrees]
            simp [Nat.pow_succ]
          have htake : (trees.take k).length = 2 ^ h := by
            rw [List.length_take, hk, htrees, Nat.pow_succ]
            omega
          have hdrop : (trees.drop k).length = 2 ^ h := by
            rw [List.length_drop, hk, htrees, Nat.pow_succ]
            omega

          rcases fromTreesDivO_exists_pow2 f (trees.take k) h htake with
            ⟨l, hl⟩
          rcases fromTreesDivO_exists_pow2 f (trees.drop k) h hdrop with
            ⟨r, hr⟩

          refine ⟨node (f l.value r.value) l r, ?_⟩
          simp only [fromTreesDivO, hlen, Nat.pow_succ, trees, hk] at hl hr ⊢
          simp [hl, hr]

private theorem fromTreesDivO_isSome_pow2
    (f : H → H → H)
    (trees : List (HashTree H))
    (h : Nat) :
    trees.length = 2 ^ h → (fromTreesDivO f trees).isSome :=
  by
    rw [Option.isSome_iff_exists]
    apply fromTreesDivO_exists_pow2

private def fromTreesDiv
    (f : H → H → H)
    (trees : List (HashTree H))
    (trees_pow2 : ∃ h : Nat, trees.length = 2 ^ h) :=
  (fromTreesDivO f trees).get
  (by
    rcases trees_pow2 with ⟨h, hlen⟩
    apply fromTreesDivO_isSome_pow2 f trees h hlen)

end HashTree
