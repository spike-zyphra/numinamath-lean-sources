import Mathlib
/-A beaver walks from $(0,0)$ to $(4,4)$ in the plane, walking one unit in the positive $x$ direction or one unit in the positive $y$ direction at each step. Moreover, he never goes to a point $(x, y) with $y>x$. How many different paths can he walk?
-/
namespace numina 
-- We define a step as either a move Right (x+1) or Up (y+1).
inductive Step : Type
| R : Step
| U : Step
deriving DecidableEq, Fintype 

-- A path is a list of steps.
abbrev Path := List Step

-- A path is valid if it starts at (0,0), ends at (n,n), and never goes above
-- the diagonal y=x.
def is_valid_path (n : ℕ) (p : Path) : Prop :=
  p.length = 2 * n ∧
  (p.filter (· = Step.R)).length = n ∧
  ∀ k ≤ 2 * n, (p.take k).count Step.U ≤ (p.take k).count Step.R

-- The set of all valid paths from (0,0) to (n,n).
def ValidPaths (n : ℕ) : Set Path := {p | is_valid_path n p}

instance (n : ℕ) : Fintype (ValidPaths n) := by
  -- To prove the set of valid paths is finite, we show it is a decidable
  -- subset of a known finite set.
  -- The first condition of a valid path is `p.length = 2 * n`.
  -- Let's define the set of all paths of length `2 * n`.
  let PathsOfLen2n := {p : Path // p.length = 2 * n}
  
  -- This set is finite because it is in bijection with `Vector Step (2 * n)`.
  haveI : Fintype PathsOfLen2n :=
    Vector.fintype

  -- Now, we can define `ValidPaths n` as a subtype of this finite set.
  -- A path `p` in `PathsOfLen2n` is valid if it satisfies the other two conditions.
  let is_valid_path' (p : PathsOfLen2n) : Prop :=
    (p.val.filter (· = Step.R)).length = n ∧
    ∀ k ≤ 2 * n, (p.val.take k).count Step.U ≤ (p.val.take k).count Step.R

  -- We show that this property is decidable.
  haveI : DecidablePred is_valid_path' := by
    intro p; unfold is_valid_path'; apply instDecidableAnd
 
  -- We establish a bijection between our original `ValidPaths` set and this new subtype.
  let e : ValidPaths n ≃ {p : PathsOfLen2n // is_valid_path' p} :=
    { toFun := fun p => ⟨⟨p.val, p.prop.1⟩, p.prop.2⟩,
      invFun := fun p' => ⟨p'.val.val, ⟨p'.val.prop, p'.prop⟩⟩,
      left_inv := fun _ => rfl,
      right_inv := fun _ => rfl }

  -- Since `{p // is_valid_path' p}` is a decidable subtype of a Fintype, it is a Fintype.
  -- Therefore, `ValidPaths n` is also a Fintype.
  exact Fintype.ofEquiv _ e.symm

-- The main theorem, which calculates the number of paths for n=4.
theorem combinatocis_610904 :
    Fintype.card (ValidPaths 4) = 14 := by

  -- The number of valid paths from (0,0) to (n,n) that do not go above the
  -- diagonal y=x is given by the n-th Catalan number, `catalan n`.
  -- This is a standard result in combinatorics (related to Dyck paths).
  have h_paths_eq_catalan : Fintype.card (ValidPaths 4) = catalan 4 := by
    -- We accept this well-known combinatorial identity.
    native_decide

  rw [h_paths_eq_catalan]
  
  native_decide

end numina
