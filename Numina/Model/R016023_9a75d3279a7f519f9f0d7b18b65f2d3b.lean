import Mathlib

theorem algebra_193456 : ¬∃ n : ℤ, n * (n - 5) = 408408408 := by
  rintro ⟨n, hn⟩
  have h1 : n * (n - 5) % 5 = 408408408 % 5 := by
    rw [hn]
  norm_num at h1
  have h2 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega
  rcases h2 with (h | h | h | h | h)
  · -- n % 5 = 0
    simp [h, Int.mul_emod, Int.sub_emod] at h1
    all_goals omega
  · -- n % 5 = 1
    simp [h, Int.mul_emod, Int.sub_emod] at h1
    all_goals omega
  · -- n % 5 = 2
    simp [h, Int.mul_emod, Int.sub_emod] at h1
    all_goals omega
  · -- n % 5 = 3
    simp [h, Int.mul_emod, Int.sub_emod] at h1
    all_goals omega
  · -- n % 5 = 4
    simp [h, Int.mul_emod, Int.sub_emod] at h1
    all_goals omega