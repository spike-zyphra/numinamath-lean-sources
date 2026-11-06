import Mathlib

open Real

/- 12. (1989 Irish Mathematical Olympiad) Let $a$ be a positive real number, $b=\left(a+\sqrt{a^{2}+1}\right)^{\frac{1}{3}}+\left(a-\sqrt{a^{2}+1}\right)^{\frac{1}{3}}$, prove that: $b$ is a positive integer if and only if $a$ is a positive integer of the form $\frac{1}{2} n\left(n^{2}+3\right)$ where $\left(n \in \mathbf{N}_{+}\right)$. -/
namespace algebra_129968

noncomputable def cbrt (x : ℝ) :=
  -- from https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/How.20to.20prove.20.28x.5E.20.281.2F3.20.3A.20.E2.84.9D.29.29.5E.283.3A.E2.84.9D.29.20.3D.20x/near/514905792
  SignType.sign x * |x| ^ (1 / 3 : ℝ)

lemma cbrt_pow_3 (x : ℝ) : (cbrt x) ^ 3 = x := by
  simp [cbrt]
  ring_nf
  norm_cast
  have : SignType.sign x ^ 3 = SignType.sign x := by
    unfold SignType.sign
    simp
    rfl
  rw [this]
  have : (|x| ^ (1 / 3 : ℝ)) ^ 3 = |x| := by
    have : |x| ≥ 0 := by
      simp
    generalize |x| = x at this
    have pow_ℕ_eq_pow_ℝ (x : ℝ) : x ^ 3 = x ^ (3 : ℝ) := by
      have : (3 : ℝ) = (3 : ℕ) :=
        rfl
      rw [this]
      exact Eq.symm (rpow_natCast x 3)
    rw [pow_ℕ_eq_pow_ℝ]
    --ring
    have : (x ^ (1 / 3 : ℝ)) ^ (3 : ℝ) = x ^ ((1 / 3) * 3 : ℝ) := by
      exact Eq.symm (rpow_mul this (1 / 3) 3)
    rw [this]
    simp
  rw [this]
  exact sign_mul_abs x

lemma mul_cbrt_eq_cbrt_mul (x y : ℝ) : cbrt x * cbrt y = cbrt (x * y) := by
  unfold cbrt
  ring_nf
  have : SignType.sign (x * y) = SignType.sign x * SignType.sign y := by
    exact sign_mul x y
  rw [this]
  have : |x * y| ^ (1 / 3 : ℝ) = |x| ^ (1 / 3 : ℝ) * |y| ^ (1 / 3 : ℝ) := by
    have : |x * y| = |x| * |y| := by
      exact abs_mul x y
    rw [this]
    refine mul_rpow ?_ ?_ <;>
    . simp
  rw [this]
  push_cast
  ring

theorem algebra_129968 (a : ℝ) (ha : a > 0)
    (b : ℝ) (hba : b = cbrt (a + √(a^2 + 1)) + cbrt (a - √(a^2 + 1))) :
    (b > 0 ∧ ∃ m : ℕ, m > 0 ∧ b = m) ↔
    ∃ n : ℕ, n > 0 ∧ a = (1 / 2) * n * (n^2 + 3) := by
  have b_pow_3_add_3_b_eq_2_a : b ^ 3 + 3 * b = 2 * a := by
    set α := cbrt (a + √(a^2 + 1))
    set β := cbrt (a - √(a^2 + 1))
    have cube_eq := congrArg (. ^ 3) hba
    simp at cube_eq
    ring_nf at cube_eq
    have b_pow_3_eq : b ^ 3 = α ^ 3 + β ^ 3 + 3 * (α * β) * b := by
      --nlinarith
      rw [cube_eq, hba]
      ring
    have : α ^ 3 = a + √(a^2 + 1) := by
      unfold α --simp [α]
      exact cbrt_pow_3 (a + √(a ^ 2 + 1))
    rw [this] at b_pow_3_eq
    have : β ^ 3 = a - √(a^2 + 1) := by
      unfold β
      exact cbrt_pow_3 (a - √(a ^ 2 + 1))
    rw [this] at b_pow_3_eq
    have : α * β = -1 := by
      unfold α β
      rw [mul_cbrt_eq_cbrt_mul]
      have : (a + √(a ^ 2 + 1)) * (a - √(a ^ 2 + 1)) = -1 := by
        ring_nf
        have := sq_sqrt (by nlinarith : 1 + a ^ 2 ≥ 0)
        rw [this]
        ring
      rw [this]
      norm_num [cbrt]
    rw [this] at b_pow_3_eq
    ring_nf at b_pow_3_eq
    linarith
  clear hba
  constructor
  . simp
    intro b_pos m m_pos b_eq_m
    subst b_eq_m
    --norm_cast at b_pow_3_add_3_b_eq_2_a
    have : 2 ∣ m ^ 3 + 3 * m := by
      have := Nat.div_add_mod m 2
      rw [← this]
      mod_cases m % 2 <;>
      . rw [H]
        ring_nf
        omega
    rcases this with ⟨n, f_m_eq_2_n⟩
    use m
    constructor
    . exact m_pos
    . linarith
  . simp
    intro m m_pos a_eq
    subst a_eq
    ring_nf at b_pow_3_add_3_b_eq_2_a
    have : b = m := by
      let f (b : ℝ) := b * 3 + b ^ 3
      change f b = f m at b_pow_3_add_3_b_eq_2_a
      have : f.Injective := by
        /-
        suffices StrictMono f by
          exact this.injective
         -/
        simp [Function.Injective, f]
        intro x y eq
        have diff_eq_0 : (x - y) * (x ^ 2 + x * y + y ^ 2 + 3) = 0 := by
          linarith
        simp at diff_eq_0
        cases diff_eq_0
        . linarith
        . exfalso
          nlinarith
      exact this b_pow_3_add_3_b_eq_2_a
    simp [this]
    exact m_pos

end algebra_129968
open algebra_129968
