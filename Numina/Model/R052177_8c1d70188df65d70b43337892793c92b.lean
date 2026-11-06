import Mathlib

theorem number_theory_245331 {a d : ℚ} (hd : d > 0) :
    ∃ q : ℚ, a / d = q ↔ ∃ r : ℚ, ∃ n : ℕ, a + (n - 1) * d = r ^ n := by
  use a / d
  constructor
  · -- Assume h: a/d = a/d, prove ∃ r n: a + (n-1) * d = r^n
    rintro h
    use a
    use 1
    simp
    all_goals ring_nf
  · -- Assume ∃ r n: a + (n-1) * d = r^n, prove a/d = a/d
    rintro ⟨r, ⟨n, hn⟩⟩
    -- We already defined q as a/d, so equality holds
    simpa using by field_simp