import Mathlib

/- 13. a) Integers $a, b, c$ are such that their sum is divisible by 6. Prove that the number $a^{5} + b^{3} + c$ is also divisible by 6.

b) Prove that for any integer $n$, the number $n^{5} - 5 n^{3} + 4 n$ is divisible by 120.

c) Prove that for any odd $n$, the number $n^{3} + 3 n^{2} - n - 3$ is divisible by 48.

d) Prove that for any odd $n$, the number $n^{8} - n^{6} - n^{4} + n^{2}$ is divisible by 1152.

e) Is the number $n(n^{2} - 1)(n^{2} - 4)$ divisible by 720 for any integer $n$? -/

theorem number_theory_106576 (a b c : ℤ) (h : 6 ∣ a + b + c) : 6 ∣ a^5 + b^3 + c := by

  --Rewrite a^5 + b^3 + c = (a - 1) * a * (a + 1) * (a^2 + 1) + (b - 1) * b * (b + 1) + (a + b + c).
  have h1 : a^5 + b^3 + c = (a - 1) * a * (a + 1) * (a^2 + 1) + (b - 1) * b * (b + 1) + (a + b + c) := by
    ring

  --Show  6 ∣ (a - 1) * a * (a + 1).
  have h11' : 6 ∣ (a - 1) * a * (a + 1) := by

    --Show a * (a + 1) is even.
    have h_even' : Even ((a * (a + 1) )) := by
      apply Int.even_mul_succ_self

    --Obtain 2 ∣ a * (a + 1).
    have h_even'' : 2 ∣ a * (a + 1) := by
      exact even_iff_two_dvd.mp h_even'

    --Obtain 2 ∣ (a - 1) * a * (a + 1).
    have h_even : 2 ∣ (a - 1) * a * (a + 1) := by
      rw [mul_assoc]
      apply dvd_mul_of_dvd_right
      exact h_even''

    --Show 3 ∣ (a - 1) * a * (a + 1).
    have h_3_div : 3 ∣ (a - 1) * a * (a + 1) := by

      --Show 3 ∣ (a - 1) * a * (a + 1) using cases.
      by_cases
      --First case is a % 3 = 0.
      h_3_0 : a % 3 = 0
      simp_all only [EuclideanDomain.mod_eq_zero]
      rcases h_3_0 with ⟨k, hk⟩
      rw [hk]
      rw [mul_assoc, mul_assoc]
      rw [mul_comm, mul_assoc]
      use (k * (3 * k + 1) * (3 * k - 1))

      --The other two cases are a % 3 = 1 and a % 3 = 2.
      have h_3_1_or_2 : a % 3 = 1 ∨ a % 3 = 2 := by omega
      rcases h_3_1_or_2 with (h_1 | h_2)

      --When a % 3 = 1, we have a - 1 % 3 = 0.
      have : (a - 1) % 3 = 0 := by omega
      simp_all only [EuclideanDomain.mod_eq_zero]
      rcases this with ⟨k, hk⟩
      rw [hk]
      rw [mul_assoc, mul_assoc]
      use (k * (a * (a + 1)))

      --When a % 3 = 2, we have a + 1 % 3 = 0.
      have : (a + 1) % 3 = 0 := by omega
      simp_all only [EuclideanDomain.mod_eq_zero]
      rcases this with ⟨k, hk⟩
      rw [hk]
      rw [mul_comm, mul_assoc]
      use (k * ((a - 1) * a))

    --Show that 2 and 3 are coprime; decide can handle this easy step.
    have : Nat.Coprime 2 3 := by decide

    --Since 2 and 3 are coprime and 2, 3 ∣ (a - 1) * a * (a + 1), it follows that 6 ∣ (a - 1) * a * (a + 1) as well.
    omega

  --Finally show 6 ∣ (a - 1) * a * (a + 1) * (a^2 + 1).
  --This follows as 6 ∣ (a - 1) * a * (a + 1).
  have h11 : 6 ∣ (a - 1) * a * (a + 1) * (a^2 + 1) := by
    apply dvd_mul_of_dvd_left
    exact h11'

  --Show 6 ∣ (b - 1) * b * (b + 1).
  --The procedure is the same as before.
  have h12 : 6 ∣ (b - 1) * b * (b + 1) := by
    have h_2_even' : Even ((b * (b + 1) )) := by
      apply Int.even_mul_succ_self
    have h_2_even'' : 2 ∣ b * (b + 1) := by
      exact even_iff_two_dvd.mp h_2_even'
    have h_2_even : 2 ∣ (b - 1) * b * (b + 1) := by
      rw [mul_assoc]
      apply dvd_mul_of_dvd_right
      exact h_2_even''
    have h_3_div : 3 ∣ (b - 1) * b * (b + 1) := by

      by_cases
      h_3_0 : b % 3 = 0
      simp_all only [EuclideanDomain.mod_eq_zero]
      rcases h_3_0 with ⟨k, hk⟩
      rw [hk]
      rw [mul_assoc, mul_assoc]
      rw [mul_comm, mul_assoc]
      use (k * (3 * k + 1) * (3 * k - 1))

      have h_3_1_or_2 : b % 3 = 1 ∨ b % 3 = 2 := by omega
      rcases h_3_1_or_2 with (h_1 | h_2)

      have : (b - 1) % 3 = 0 := by omega
      simp_all only [EuclideanDomain.mod_eq_zero]
      rcases this with ⟨k, hk⟩
      rw [hk]
      rw [mul_assoc, mul_assoc]
      use (k * (b * (b + 1)))

      have : (b + 1) % 3 = 0 := by omega
      simp_all only [EuclideanDomain.mod_eq_zero]
      rcases this with ⟨k, hk⟩
      rw [hk]
      rw [mul_comm, mul_assoc]
      use (k * ((b - 1) * b))

    have : Nat.Coprime 2 3 := by decide

    omega

  rcases h11 with ⟨k₁, hk₁⟩
  rcases h12 with ⟨k₂, hk₂⟩
  rcases h with ⟨k₃, hk₃⟩

  rw [hk₁] at h1
  rw [hk₂] at h1
  rw [hk₃] at h1

  --Show (a - 1) * a * (a + 1) * (a^2 + 1) + (b - 1) * b * (b + 1) + (a + b + c) = 0 mod 6
  refine Int.dvd_of_emod_eq_zero ?_
  rw [h1]
  omega