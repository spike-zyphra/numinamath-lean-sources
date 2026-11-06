import Mathlib

/- How many ordered triples of integers $(a,b,c)$, with $a≥2$, $b≥1$, and $C≥0$, satisfy both $\log_a(​b)=c^2005$ and $a+b+c=2005$?
(A) 0 (B) 1 (C) 2 (D) 3 (E) 4 -/
theorem number_theory_97186 :
{(a, b, c) : ℕ × ℕ × ℕ | a ≥ 2 ∧ b ≥ 1 ∧ c ≥ 0 ∧ Real.logb a b = c ^ 2005 ∧ a + b + c = 2005}.ncard = 2 := by
  -- We find explicitly the set of solutions
  suffices h : {(a, b, c) : ℕ × ℕ × ℕ | a ≥ 2 ∧ b ≥ 1 ∧ c ≥ 0 ∧ Real.logb a b = c ^ 2005 ∧ a + b + c = 2005} = {(2004, 1, 0), (1002, 1002, 1)} by rw [h]; simp
  -- Show that both inclusions hold
  apply Set.eq_of_subset_of_subset
  -- "⊆". Obtain assumptions
  intro (a, b, c) habc
  obtain ⟨ha, hb, hc, h1, h2⟩ := habc
  -- Rewrite assumption about log using powers
  have h1 : a ^ (c ^ 2005) = b := by
    rw [(Real.logb_eq_iff_rpow_eq _ _ _)] at h1
    norm_cast at h1
    all_goals norm_cast <;> linarith
  rw [←h1] at h2
  -- Case distinction on c
  match c with
  | 0 => simp at h1 h2; simp [h1, h2] -- First solution
  | 1 => simp at h1 h2; simp; omega -- Second solution
  | c + 2 => -- In this case b is too big, obtain a contradiction
    have : 2005 > 2005 := by calc
    2005 = a + a ^ (c + 2) ^ 2005 + (c + 2) := by rw [h2]
       _ > a ^ (c + 2) ^ 2005 := by omega
       _ ≥ 2 ^ (c + 2) ^ 2005 := by apply (Nat.pow_le_pow_of_le_left ha)
       _ ≥ 2 ^ 2 ^ 2005       := by apply Nat.pow_le_pow_of_le_right; simp; apply Nat.pow_le_pow_of_le_left; simp
       _ ≥ 2 ^ 2 ^ 4          := by repeat apply Nat.pow_le_pow_of_le_right; simp; apply Nat.pow_le_pow_of_le_right <;> simp
       _ > 2005               := by simp
    linarith
  -- "⊇". It is an easy calculation that the two triples satisfy the conditions
  intro (a, b, c) habc
  simp; simp at habc; cases habc <;> simp [*]