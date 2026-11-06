import Mathlib

/- 1. Given that $n$ and $s$ are integers, if for any integer $n$, the equation $x^{2}-8 n x+7^{s}=0$ has no integer solutions, the set of all such numbers $s$ is $\qquad$ . -/
theorem number_theory_187450 (s : ℕ) :
    (∀ n : ℤ, ¬∃ x : ℤ, x^2 - 8 * n * x + 7^s = 0) ↔ Even s := by
  -- ∃ x : ℤ, x^2 - 8 * n * x + 7^s = 0 is equivalent to
  -- ∃ p q : ℤ, p + q = b ∧ p * q = c
  have hpq (b c : ℤ) : (∃ x, x^2 - b * x + c = 0) ↔ (∃ p q, p + q = b ∧ p * q = c) := by
    constructor
    · intro ⟨x, hx⟩
      have ⟨y, hy⟩ := vieta_formula_quadratic (pow_two x ▸ hx)
      use x, y
      tauto
    · intro ⟨p, q, hb, hc⟩
      use p
      linear_combination p * hb - hc
  simp_rw [hpq]
  clear hpq
  constructor
  · intro h
    -- assume that s is Odd and show that there exist n, p, and q such that p + q = 8 * n and p * q = 7^s
    contrapose! h
    rw [Nat.not_even_iff_odd] at h
    -- we have 1 + 7 ^ s = 0 (mod 8) since 7 ^ s = (-1) ^ s = -1 (s is Odd)
    have h8 : ((1 + 7 ^ s : ℤ) : ZMod 8) = 0 := by
      push_cast
      rw [show (7 : ZMod 8) = -1 by rfl, Odd.neg_one_pow h, add_neg_cancel]
    -- we get that 1 + 7 ^ s = 8 * n for some n
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h8
    have ⟨k, hk⟩ := h8
    -- use this n, p = 1, q = 7 ^ s and get 1 + 7 ^ s = 8 * n and 1 * 7 ^ s = 7 ^ s
    use k, 1, 7 ^ s
    simp [hk]
  · intro heven n
    push_neg
    -- now assume that s is Even and show that p + q = 8 * n implies that p * q ≠ 7 ^ s for any p and q
    have ⟨k, hk⟩ := even_iff_exists_two_mul.mp heven
    intro p q hn hs
    -- prove that p ^ 2 = -1 = 7 (mod 8)
    have : (p ^ 2 : ZMod 8) = 7 := by
      -- p = 8 * n - q = -q (mod 8)
      nth_rw 1 [pow_two, show p = 8 * n - q by linarith]
      push_cast
      rw [sub_mul, mul_comm (q : ZMod 8)]
      norm_cast
      rw [hs]
      push_cast
      -- we have p * q = 7 ^ s so -p^2 = (-1)^s (mod 8), p^2 = -1 = 7 (mod 8) since (-1) ^ s = 1
      rw [show (7 : ZMod 8) = -1 from rfl, Even.neg_one_pow heven, show (8 : ZMod 8) = 0 from rfl]
      simp
    -- consider all possible values of p mod 8
    -- for all these values, p ^ 2 ≠ 7
    mod_cases h : p % 8
    all_goals {
      rw [show (8 : ℤ) = (8 : ℕ) from rfl, ←ZMod.intCast_eq_intCast_iff] at h
      simp [h] at this
      norm_cast at this
    }