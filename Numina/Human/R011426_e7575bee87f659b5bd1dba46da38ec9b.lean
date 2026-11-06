import Mathlib

theorem algebra_111006 {M : Type*} {f : M → M → M} (hM : ∀ x y : M, f x (f y x) = y) : (∀ a b : M, ((∃! x : M, (f a x = b)) ∧ (∃! x : M, f x a = b))) := by 
  intro a b
  constructor
  use (f b a)
  simp
  constructor
  exact hM a b
  intro y hy
  have yeq : a = f y (f a y) := by 
    apply Eq.symm
    exact hM y a
  have eq2 : f b a = y := by 
    calc 
      _ = f b (f y b) := by 
        rw [hy] at yeq
        rw [←yeq]
      _ = y := by 
        exact hM b y
  exact Eq.symm eq2
  use (f a b)
  constructor
  simp
  have aeq : a = f b (f a b) := by 
    exact Eq.symm (hM b a)
  nth_rw 2 [aeq]
  exact hM (f a b) b
  intro y hy
  have yeq : y = f a b := by 
    rw [←hy]
    exact Eq.symm (hM a y)
  exact yeq