import Mathlib
import Aesop

/-A rectangle is called cool if the number of square units in its area is equal to twice the number of units in its perimeter. A cool rectangle also must have integer side lengths. What is the sum of all the different possible areas of cool rectangles?-/
theorem algebra_14646 : ∃(S: Set (ℕ × ℕ)), S = { (a, b) | 0 < a ∧ 0 < b ∧ a ≤ b ∧ a * b = 2 * (2 * a + 2 * b) } ∧ ∃(r : Finset (ℕ × ℕ)), r = S ∧ ∑ p ∈ r, p.1 * p.2 = 236 := by
  simp
  use { (5, 20), (6, 12), (8, 8) }
  simp
  ext ⟨a, b⟩
  simp
  constructor
  · rintro (h | h | h)
    repeat rw [h.1, h.2]; norm_num
  · rintro ⟨ha, hb, hab, h⟩
    have ha: 5 ≤ a := by
      by_cases h: a ≤ 5
      · interval_cases a <;> linarith
      linarith
    have hb: 5 ≤ b := by
      by_cases h: b ≤ 5
      · interval_cases b <;> linarith
      linarith
    -- Let the side lengths of the rectangle be $a$ and $b.$ It follows that $ab=4(a+b).$ Expanding and moving all the terms to the left hand side, $ab-4a-4b=0.$ Adding 16 to both sides allows us to factor: a(b-4)-4(b-4)=(a-4)(b-4)=16.
    have h: ((a - 4) * (b - 4) : ℕ) = (16 : ℝ) := by
      have : ((a - 4) * (b - 4) : ℕ) = a * b - 4 * a - 4 * b + (16 : ℝ):= by
        simp
        rw [Nat.cast_sub (by linarith), Nat.cast_sub (by linarith)]
        simp
        linarith
      rw [this, ←Nat.cast_mul, h]
      simp
      linarith
    norm_cast at h

    obtain ⟨c, hc⟩ := show ∃c, c = a - 4 by simp
    obtain ⟨d, hd⟩ := show ∃d, d = b - 4 by simp
    rw [hc.symm, hd.symm] at h
    have : a = c + 4 := by omega
    rw [this]
    have : b = d + 4 := by omega
    rw [this]
    -- so, c * d = 16, and c, d are both positive integers
    have p_c : c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 16 := by
      have := Nat.mem_divisors.mpr (And.intro (Dvd.intro d h) (by positivity))
      have set_divisors : Nat.divisors 16 = {1, 2, 4, 8, 16} := by rfl
      rw [set_divisors] at this
      simp at this
      exact this
    -- From this point, the pairs $(a,b)$ that provide different areas are $(5,20),$ $(6,12),$ and $(8,8),$ and the sum of the possible areas is $\boxed{236}.$
    obtain (r | r | r | r | r) := p_c
    . -- c = 1
      have : d = 16 := by rw [r] at h; linarith
      rw [this, r]
      norm_num
    . -- c = 2
      have : d = 8 := by rw [r] at h; linarith
      rw [this, r]
      norm_num
    . -- c = 4
      have : d = 4 := by rw [r] at h; linarith
      rw [this, r]
      norm_num
    . -- c = 8
      rename_i hc
      have hd: d = 2 := by rw [r] at h; linarith
      rw [r] at hc
      rw [hd] at this
      linarith
    . -- c = 16
      rename_i hc
      have hd: d = 1 := by rw [r] at h; linarith
      rw [r] at hc
      rw [hd] at this
      linarith
