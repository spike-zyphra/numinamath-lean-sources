import Mathlib

theorem algebra_208250 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : ∃ x y, x^2 + p * x + q = 0 ∧ y^2 + p * y + q = 0 ∧ |(x : ℤ) - y| = 1) :
    p = 3 ∧ q = 2 := by 
  rcases h with ⟨x, y, hx, hy, hxy⟩
  have h1 : (x : ℤ) ^ 2 + (p : ℤ) * (x : ℤ) + (q : ℤ) = 0 := by
    exact_mod_cast hx
  have h2 : (y : ℤ) ^ 2 + (p : ℤ) * (y : ℤ) + (q : ℤ) = 0 := by
    exact_mod_cast hy
  have h3 : (x : ℤ) - (y : ℤ) ≠ 0 := by
    have h3 : |(x : ℤ) - (y : ℤ)| = 1 := hxy
    by_contra h
    have : (x : ℤ) - (y : ℤ) = 0 := by omega
    rw [this] at h3
    norm_num at h3
  have eq1 : (x : ℤ) ^ 2 + (p : ℤ) * (x : ℤ) = (y : ℤ) ^ 2 + (p : ℤ) * (y : ℤ) := by
    linarith
  have eq2 : ((x : ℤ) - (y : ℤ)) * ((x : ℤ) + (y : ℤ) + (p : ℤ)) = 0 := by
    linarith
  cases (mul_eq_zero.mp eq2) with
  | inl h4 =>
    exfalso
    apply h3
    linarith
  | inr h5 =>
    have h4 : (x : ℤ) + (y : ℤ) = - (p : ℤ) := by
      linarith [h5]
    have h5 : (x + y : ℤ) = - (p : ℤ) := by
      have h6 : (x : ℤ) + (y : ℤ) = - (p : ℤ) := by
        linarith [h5]
      have h7 : (x + y : ℤ) = (x : ℤ) + (y : ℤ) := by
        simp
      rw [h7]
      linarith [h6]
    -- contradiction
    have h7' : (x : ℤ) ≥ 0 := by
      exact_mod_cast show x ≥ 0 by omega
    have h8' : (y : ℤ) ≥ 0 := by
      exact_mod_cast show y ≥ 0 by omega
    have h9' : (x + y : ℤ) ≥ 0 := by
      omega
    -- The quadratic formula tells us that (x + y) = -p, which implies p divides x+y
    have h10' : (p : ℤ) ≥ 2 := by
      exact_mod_cast (show p ≥ 2 by
        by_contra h
        push_neg at h
        have : p < 2 := by omega
        interval_cases p <;> norm_num at hp <;> tauto
      )
    -- contradiction
    have h11' : (p : ℤ) ≤ 0 := by
      linarith [h5, h9']
    linarith