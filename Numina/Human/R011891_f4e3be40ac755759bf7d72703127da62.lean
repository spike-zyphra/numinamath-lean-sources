import Mathlib

/-.4. 104 Find the integer solutions of the system of equations
$$\left\{\begin{array}{l}
x z-2 y t=3 \\
x t+y z=1
\end{array}\right.$$-/
theorem number_theory_248298 : {(x, y, z, t) : ℤ×ℤ×ℤ×ℤ | x * z - 2 * y * t = 3 ∧ x * t + y * z = 1} = {(1, 0, 3, 1), (-1, 0, -3, -1), (3, 1, 1, 0), (-3, -1, -1, 0)} := by
  ext ⟨x, y, z, t⟩; simp
  refine ⟨?_, λh ↦ by
    obtain ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ := h
    all_goals norm_num
  ⟩
  rintro ⟨h₁, h₂⟩
  have h₃ : (x^2 + 2 * y^2) * (z^2 + 2 * t^2) = 11 := by nlinarith
  have h₄ : Prime (11 : ℤ) := by
    apply Int.prime_ofNat_iff.mpr
    native_decide
  rw [←h₃, Int.prime_iff_natAbs_prime, Int.natAbs_mul, Nat.prime_mul_iff] at h₄
  obtain ⟨h₄, h₅⟩ | ⟨h₄, h₅⟩ := h₄ <;>
    rw [Int.natAbs_eq_iff] at h₅ <;>
    norm_num at h₅ <;>
    obtain h₅ | h₅ := h₅
  · -- z ^ 2 + 2 * t ^ 2 = 1
    have : z^2 = 1 := by
      have h₆ : z^2 ≤ 1 := by rw [h₅.symm]; nlinarith
      have h₇ : z^2 ≠ 0 := by omega
      have h₈ := sq_nonneg z
      omega
    simp at this
    obtain h₆ | h₆ := this
    all_goals
    · rw [h₆] at h₁ h₂ h₅ ⊢
      simp at h₁ h₂ h₅ ⊢
      rw [h₅] at h₁ h₂ ⊢
      simp at h₁ h₂ ⊢
      exact ⟨by linarith, by linarith⟩
  · -- z ^ 2 + 2 * t ^ 2 = -1, which is impossible
    nlinarith
  · -- x ^ 2 + 2 * y ^ 2 = 1
    have : x^2 = 1 := by
      have h₆ : x^2 ≤ 1 := by rw [h₅.symm]; nlinarith
      have h₇ : x^2 ≠ 0 := by omega
      have h₈ := sq_nonneg x
      omega
    simp at this
    obtain h₆ | h₆ := this
    all_goals
    · rw [h₆] at h₁ h₂ h₅ ⊢
      simp at h₁ h₂ h₅ ⊢
      rw [h₅] at h₁ h₂ ⊢
      simp at h₁ h₂ ⊢
      exact ⟨by linarith, by linarith⟩
  · -- x ^ 2 + 2 * y ^ 2 = -1, which is impossible
    nlinarith
