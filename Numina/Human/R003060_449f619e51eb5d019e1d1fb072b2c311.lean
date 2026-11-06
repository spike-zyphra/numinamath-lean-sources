import Mathlib

/- ## Task 33/67

Prove: If three natural numbers $x ; y ; z$, which have no common divisor, satisfy the condition $x^{2}+y^{2}=z^{2}$ (so-called primitive Pythagorean triple), then $x$ and $y$ cannot both be odd. -/
theorem number_theory_149724 {x y z : ℕ} (h₀ : Nat.Coprime x y) (h₁ : Nat.Coprime y z)
    (h₂ : Nat.Coprime x z) (h₃ : x^2 + y^2 = z^2) :
    ¬(Odd x ∧ Odd y)
  := by
    -- assume that both x and y are odd
    by_contra h
    have ⟨xh, yh⟩ := h

    -- then x ^ 2 is odd
    have x_sq : Odd (x ^ 2) := Odd.pow xh
    -- and y ^ 2 is odd
    have y_sq : Odd (y ^ 2) := Odd.pow yh

    -- so z ^ 2 is even
    have z_sq : Even (z ^ 2) := h₃ ▸ Odd.add_odd x_sq y_sq

    -- so z is even
    have zh : Even z := by
      -- assume it's not even
      by_contra not_even
      -- then z ^ 2 is not even
      have z_sq' : ¬Even (z ^ 2) := by
        norm_num at not_even ⊢
        exact not_even.pow
      -- but we just showed that it's even, contradiction
      contradiction

    -- so x = 2 * k + 1
    obtain ⟨k, kh⟩ : ∃ k, x = 2 * k + 1 := xh

    -- y = 2 * l + 1
    obtain ⟨l, lh⟩ : ∃ l, y = 2 * l + 1 := yh
    -- z = 2 * l
    obtain ⟨m, mh⟩ : ∃ m, z = 2 * m := zh.exists_two_nsmul
    rw [kh, lh, mh] at h₃

    -- grouping terms we have
    -- 4 * (k ^ 2 + l ^ 2 + k + l) + 2 = 4 * m ^ 2
    have grouped : 4 * (k ^ 2 + l ^ 2 + k + l) + 2 = 4 * m ^ 2 := by linarith

    -- and four divides the RHS
    have four_dvd : 4 ∣ 4 * m ^ 2 := Nat.dvd_mul_right 4 (m ^ 2)

    -- but it does not divide the LHS
    have four_not_dvd : ¬4 ∣ 4 * m ^ 2 := by
      -- because four divides 4 * (k ^ 2 + l ^ 2 + k + l)
      have left_dvd := Nat.dvd_mul_right 4 (k ^ 2 + l ^ 2 + k + l)
      rw [←grouped, ←Nat.dvd_add_iff_right left_dvd]
      -- but 4 does not divide 2
      norm_num

    -- so we have a contradiction
    contradiction