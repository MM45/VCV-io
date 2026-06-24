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

private theorem fromTreesO_isSome
    (f : H → H → H)
    (trees : List (HashTree H)) :
    trees ≠ [] → (fromTreesO f trees).isSome :=
  match trees with
  | [] => by
      intro f
      contradiction
  | [tree] => by
      simp [fromTreesO]
  | l :: r :: trees => by
      intro _
      rw [fromTreesO]
      exact fromTreesO_isSome f
            (incLevel f (l :: r :: trees))
            (by simp [incLevel])
termination_by trees.length
decreasing_by
  exact incLevel_length_lt f l r trees

def fromTrees
    (f : H → H → H)
    (trees : List (HashTree H))
    (trees_nonnil : trees ≠ []) : HashTree H :=
  (fromTreesO f trees).get (fromTreesO_isSome f trees trees_nonnil)

end HashTree
