import Mathlib

open Real
/-Michael is playing basketball. He makes
10
%
10% of his shots, and gets the ball back after
90
%
90% of his missed shots. If he does not get the ball back he stops playing. What is the probability that Michael eventually makes a shot?-/
theorem algebra_609593 :
  (∑' i : ℕ, (9/10)^(2*i + 1) * (1/10)) = 9/19 := by
  let a:ℝ := 9/10
  let r:ℝ := (9/10)^2
  let c:ℝ := 1/10
  have h1 : r = 81/100 := by
    simp [r]
    nlinarith
  have h2 : (∑' i : ℕ, (c*(a^(2*i + 1)))) = c * a * (∑' i : ℕ, (r^i)) := by
    calc
      (∑' i : ℕ, (c*(a^(2*i + 1)))) = c * (∑' i : ℕ, (a^(2*i + 1))) := by
        rw [tsum_mul_left]
      _ = c * (∑' i : ℕ, (a^(2*i) * a)) := by
        have h : ∀ i : ℕ, a^(2*i + 1) = a^(2*i) * a := by
          intro i
          rw [pow_add]
          linarith
        simp [h]
      _ = c *(∑' i : ℕ, (a*a^(2*i)))  := by
        have h : ∀ i : ℕ, a^(2*i)*a=a*a^(2*i) := by
          intro i
          linarith
        simp [h]
      _ = c * a * (∑' i : ℕ, (a^(2*i))) := by
        rw [tsum_mul_left]
        linarith
      _ = c * a * (∑' i : ℕ, (r^i)) := by
        have h : ∀ i : ℕ, a^(2*i) = r^i := by
          intro i
          have h1 : r = a^2 := by
            norm_num
          rw [h1]
          rw [pow_mul]
        simp [h]
  have h3 : r < 1 := by
    rw [h1]
    norm_num
  have h33 : 0 ≤ r := by
    rw [h1]
    norm_num
  have h4 : (∑' i : ℕ, r^i) = 1 / (1 - r) := by
    rw [tsum_geometric_of_lt_one h33 h3]
    linarith
  have h5 : (∑' i : ℕ, (c*a^(2*i + 1))) = (c * a) / (1 - r) := by
    rw [h2, h4]
    simp
    linarith
  unfold a c r at h5
  simp[h5]
