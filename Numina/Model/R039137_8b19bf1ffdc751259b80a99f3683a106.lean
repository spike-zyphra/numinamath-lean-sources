import Mathlib

theorem number_theory_4657 (m n : ℕ) (a b : Fin n → ℤ)
                           (hm : m > 0)
                           (hequiv : ∀ j : Fin n, a j ≡ b j [ZMOD m]) :
                           ∑ j : Fin n, a j ≡ ∑ j : Fin n, b j [ZMOD m] ∧
                           ∏ j : Fin n, a j ≡ ∏ j : Fin n, b j [ZMOD m] := by
  constructor
  · -- Show that $\sum a_j \equiv \sum b_j \pmod{m}$
    -- Let's compute the congruence of the sums
    have h1 : ∀ j : Fin n, a j % (m : ℤ) = b j % (m : ℤ) := by
      intro j 
      have h := hequiv j
      simp [Int.ModEq] at h ⊢
      all_goals omega

    have h2 : (∑ j : Fin n, a j) % (m : ℤ) = (∑ j : Fin n, b j) % (m : ℤ) := by
      have h4 : ∀ j : Fin n, a j % (m : ℤ) = b j % (m : ℤ) := h1
      simp [Finset.sum_int_mod, h4]
    
    -- Now we can compute the congruence from the modulo equality
    show ∑ j : Fin n, a j ≡ ∑ j : Fin n, b j [ZMOD m]
    simp [Int.ModEq]
    all_goals omega
  · -- Show that $\prod a_j \equiv \prod b_j \pmod{m}$
    -- Let's compute the congruence of the products
    have h1 : ∀ j : Fin n, a j % (m : ℤ) = b j % (m : ℤ) := by
      intro j 
      have h := hequiv j
      simp [Int.ModEq] at h ⊢
      all_goals omega

    have h2 : (∏ j : Fin n, a j) % (m : ℤ) = (∏ j : Fin n, b j) % (m : ℤ) := by
      have h4 : ∀ j : Fin n, a j % (m : ℤ) = b j % (m : ℤ) := h1
      simp [Finset.prod_int_mod, h4]
    
    -- Now we can compute the congruence from the modulo equality
    show ∏ j : Fin n, a j ≡ ∏ j : Fin n, b j [ZMOD m]
    simp [Int.ModEq]
    all_goals omega