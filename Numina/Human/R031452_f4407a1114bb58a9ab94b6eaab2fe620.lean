import Mathlib

/- 1.56 When $x=-1, x=0, x=1, x=2$, the polynomial
$$
P(x)=a x^{3}+b x^{2}+c x+d
$$
takes integer values. Prove that for all integer values of $x$, this polynomial takes integer values.
(14th All-Russian Mathematical Olympiad, 1988) -/
theorem algebra_114910 {a b c d : ℝ}
    (h : ∀ x ∈ Set.Icc (-1 : ℤ) 2, ∃ n : ℤ, a * x^3 + b * x^2 + c * x + d = n) :
    ∀ x : ℤ, ∃ n : ℤ, a * x^3 + b * x^2 + c * x + d = n := by
  -- We have a * x^3 + b * x^2 + c * x + d
  --   = 6 * a * ((x - 1) * x * (x + 1) / 6) + 2 * b * (x * (x - 1) / 2) + (a + b + c) * x + d
  -- for all x.
  have heq x : a * x^3 + b * x^2 + c * x + d =
                6 * a * ((x - 1) * x * (x + 1) / 6) + 2 * b * (x * (x - 1) / 2) + (a + b + c) * x + d := by ring
  -- Show that there exists d' ∈ ℤ such that d = d'.
  have ⟨d', hd⟩ : ∃ d' : ℤ, d = d' := by
    -- We have P(0) = d = n ∈ ℤ.
    have ⟨n, hn⟩ := h 0 (by simp)
    -- Take d' = n.
    use n
    simp [← hn]
  -- Show that a + b + c = s' is an integer.
  have ⟨s', hs⟩ : ∃ s' : ℤ, a + b + c = s' := by
    -- We have P(1) = (a + b + c) + d = n ∈ ℤ.
    have ⟨n, hn⟩ := h 1 (by simp)
    -- We showed that d' ∈ ℤ so n - d' ∈ ℤ.
    use n - d'
    push_cast at hn ⊢
    linarith
  -- Show that 2 * b = b' is an integer.
  have ⟨b', hb⟩ : ∃ b' : ℤ, 2 * b = b' := by
    -- We have P(-1) = 2 * b + (a + b + c) * (-1) + d = n ∈ ℤ.
    have ⟨n, hn⟩ := h (-1) (by simp)
    rw [heq] at hn
    norm_num at hn
    -- (a + b + c) = s' ∈ ℤ and d = d' ∈ ℤ, so 2 * b = n - d' + s' ∈ ℤ.
    use n - d' + s'
    simp [← hs, ← hd]
    linarith
  -- Show that 6 * a = a' is an integer.
  have ⟨a', ha⟩ : ∃ a' : ℤ, 6 * a = a' := by
    -- We have P(2) = 6 * a + 2 * b + (a + b + c) * 2 + d = n ∈ ℤ.
    have ⟨n, hn⟩ := h 2 (by simp)
    rw [heq] at hn
    norm_num at hn
    -- 2 * b = b' ∈ ℤ, a + b + c = s' ∈ ℤ, d = d' ∈ ℤ so
    -- 6 * a = n - b' - 2 * s' - d' ∈ ℤ.
    use n - b' - 2 * s' - d'
    simp [← hs, ← hb, ← hd]
    linarith
  -- Let x be an integer.
  intro x
  -- Show that 6 * a * ((x - 1) * x * (x + 1) / 6) + 2 * b * (x * (x - 1) / 2) + (a + b + c) * x + d
  -- is an integer.
  rw [heq]
  -- It is enough to show that
  -- a' * ((x - 1) * x * (x + 1) / 6) + b' * (x * (x - 1) / 2) + s' * x + d'
  -- is an integer.
  use a' * ((x - 1) * x * (x + 1) / 6) + b' * (x * (x - 1) / 2) + s' * x + d'
  push_cast [← hs, ← hd, ← hb, ← ha]
  -- It is left to show that (x - 1) * x * (x + 1) / 6 is an integer and
  -- x * (x - 1) / 2 is an integer.
  congr
  -- Show that 6 divides (x - 1) * x * (x + 1).
  · rw [Int.cast_div _ (by norm_num)]
    simp
    -- Consider (x - 1) * x * (x + 1) = 0 (mod 6).
    rw [show (6 : ℤ) = (6 : ℕ) by simp, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    generalize (x : ZMod 6) = y
    -- Consider all possible values of x (mod 6) and verify that
    -- (x - 1) * x * (x + 1) = 0 (mod 6).
    fin_cases y <;> simp <;> reduce_mod_char
  -- Show that 2 divides x * (x - 1).
  · rw [Int.cast_div _ (by norm_num)]
    simp
    -- Consider x * (x - 1) = 0 (mod 2).
    rw [show (2 : ℤ) = (2 : ℕ) by simp, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    generalize (x : ZMod 2) = y
    -- Consider all possible values of x (mod 2) and verify that
    -- x * (x - 1) = 0 (mod 2).
    fin_cases y <;> norm_num