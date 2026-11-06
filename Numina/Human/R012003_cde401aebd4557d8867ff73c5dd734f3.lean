import Mathlib

theorem number_theory_598210 (a b : ℕ) (ha : a > 0) (hb : b > 0) :
    (∃ q r : ℕ, a^2 + b^2 = q * (a + b) + r ∧ r < a + b ∧ q^2 + r = 1977) ↔
    (a = 50 ∧ b = 37) ∨ (a = 37 ∧ b = 50) ∨ (a = 50 ∧ b = 7) ∨ (a = 7 ∧ b = 50) := by
  refine Iff.intro ?_ $ by
    rintro (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
    · subst ha hb
      use 44, 41
      norm_num

  intro ⟨ q, r, ⟨ ab_eq, r_lt_ab, qr_eq ⟩ ⟩

  have q_le_44 : q ≤ 44 := by
    have : q^2 ≤ 44^2 := by
      by_contra h
      push_neg at h
      have := Nat.pow_le_pow_left (lt_of_pow_lt_pow_left' 2 h) 2
      linarith
    exact le_of_pow_le_pow_left₀ (by linarith) (by linarith) this

  have am_gm : 2*(a^2 + b^2) ≥ (a + b)^2 := by
    rw [add_sq]
    suffices 2*a*b ≤ a^2 + b^2 by
      omega
    exact two_mul_le_add_sq a b

  have r_lt_2q : r < 2 * q + 2 := by
    have : (a + b)^2 / (a + b) ≤
        (2*q * (a + b) + 2*(a+b)) / (a + b) := by
      apply Nat.div_le_div_right (by linarith)

    field_simp [sq] at this
    have : a + b ≤ ((a + b) * (2 * q + 2)) / (a + b) := by
      conv_rhs =>
        lhs; rw [mul_add (a+b), mul_comm]
        rhs; rw [mul_comm]
      exact this

    field_simp at this
    linarith

  replace qr_eq : q^2 + r = 44^2 + 41 := by linarith

  have ⟨q44, r41⟩ : q = 44 ∧ r = 41 := by
    -- Show that it doesn't hold when r > 41
    have : ¬ q < 44 := by
      intro q_lt
      have q_sq_lt : q^2 ≤ 43^2 := by
        gcongr
        exact Nat.le_of_lt_succ q_lt

      omega

    have q44 : q = 44 := by omega
    have r41 : r = 41 := by
      subst q
      exact Nat.add_left_cancel qr_eq

    exact ⟨q44, r41⟩

  subst q r
  zify at *
  generalize (a : ℤ) = a at *
  generalize (b : ℤ) = b at *

  -- Show equal to 1009
  have ab_eq : (a - 22)^2 + (b - 22)^2 = 32^2 - 15 := by
    have : (a - 22)^2 + (b - 22)^2 =
        a^2 + b^2 - 2 * 22 * (a + b) + 22^2 * 2 := by
      ring
    omega

  have bounds {u v : ℤ } : u^2 + v^2 = 32^2 - 15 → |u| < 32 ∧ |v| < 32 := by
    intro uv_eq
    have u_nonneg := sq_nonneg u
    have v_nonneg := sq_nonneg v
    have : |u| ^ 2 < 32 ^ 2 := by
      rw [sq_abs]
      linarith
    have : |v| ^ 2 < 32 ^ 2 := by
      rw [sq_abs]
      linarith

    constructor <;>
      exact lt_of_pow_lt_pow_left₀ 2 (by linarith) (by linarith)

  have {u v : ℤ} : u^2 + v^2 = 32^2 - 15 →
      (|u| = 28 ∧ |v| = 15) ∨ (|v| = 28 ∧ |u| = 15) := by
    intro eq
    have ⟨ u_lt, v_lt ⟩ := bounds eq
    have ⟨ u_low, u_high ⟩ : -32 < u ∧ u < 32 := abs_lt.mp u_lt
    replace eq : v^2 = 1009 - u^2 := by
      apply congrArg (u^2 - ·) at eq
      linear_combination -eq

    replace sqrt_eq : v.natAbs = Int.sqrt (1009 - u^2) := by
      zify at eq
      apply congrArg Int.sqrt at eq
      rwa [sq, Int.sqrt_eq] at eq

    have eq_neg : (-v)^2 = 1009 - u ^ 2 := by
      convert eq using 1
      simp

    have v_sqrt := by
      norm_num at sqrt_eq
      exact sqrt_eq

    interval_cases u
    case «28» | «15» | «-28» | «-15» =>
      norm_num at sqrt_eq
      norm_num [sqrt_eq]

    all_goals
      rcases abs_cases v with (⟨pos, _⟩ | ⟨neg, _⟩)
      · norm_num [pos] at v_sqrt
        norm_num [v_sqrt] at eq
      · norm_num [neg] at v_sqrt
        norm_num [v_sqrt] at eq_neg


  rcases @this (a - 22) (b - 22) ab_eq with ⟨a_eq, b_eq⟩
  <;> rcases abs_cases (a - 22) with (⟨a_abs, _⟩ | ⟨a_abs, _⟩)
  <;> rcases abs_cases (b - 22) with (⟨b_abs, _⟩ | ⟨b_abs, _⟩)
  all_goals omega
