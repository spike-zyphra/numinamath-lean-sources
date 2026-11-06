import Mathlib

/- The sequence a_n satisfies a_0 = 0 and
a_{n+1} = 8/5 * a_n + 6/5 * sqrt(4^n - a_n^2) for n ≥ 0.
Find the greatest integer less than or equal to a_10. -/
theorem algebra_94294 (a : ℕ → ℝ) (ha0 : a 0 = 0)
(han : ∀ n, a (n + 1) = 8 / 5 * a n + 6 / 5 * Real.sqrt (4 ^ n - (a n) ^ 2)) :
⌊a 10⌋ = 983 := by
  -- we define b_n = a_n/2^n
  let q: ∃ (b : ℕ → ℝ), a = fun n => 2^n*(b n) := by
    use fun n => (a n)/2^n; simp;
    ext n; ring_nf; simp
  obtain ⟨b, def_b⟩ := q
  -- and substitute
  simp_rw [def_b] at han
  have h:∀ (n:ℕ), b (n + 1) = 4 / 5 * b n + 3 / 5 * Real.sqrt (1 - (b n) ^ 2) := by
    intro n
    specialize han n
    have h2:=
      calc √(4 ^ n - (2 ^ n * b n) ^ 2)
      _ = √(4 ^ n - (2^(n*2)) * (b n)^2) := by ring_nf
      _ = √(4 ^ n - (2^(2*n) * (b n)^2)) := by ring_nf
      _ = √(4 ^ n - ((2^2)^n * (b n)^2)) := by norm_cast; rw [← Nat.pow_mul]
      _ = √(4 ^ n - (4^n * (b n)^2)) := by norm_num
      _ = √(4 ^ n * (1 - (b n)^2)) := by ring_nf
      _ = √(4 ^ n) * √(1 - (b n)^2) := by rw [Real.sqrt_mul (by norm_cast; exact Nat.zero_le _)]
      _ = (4^(n:ℝ))^((1:ℝ)/2) * √(1 - (b n)^2) := by rw [Real.sqrt_eq_rpow]; norm_num
      _ = 4^((n:ℝ)*(1:ℝ)/2) * √(1 - (b n)^2) := by rw [← Real.rpow_mul (by norm_num)]; ring_nf
      _ = (4^((1:ℝ)/2))^(n:ℝ) * √(1 - (b n)^2) := by rw [mul_div_assoc, mul_comm (n:ℝ), Real.rpow_mul (by norm_num)]
      _ = ((2^(2:ℝ))^((1:ℝ)/2))^n * √(1 - (b n)^2) := by norm_num
      _ = 2^n * √(1 - (b n)^2) := by rw [← Real.rpow_mul (by norm_num)]; norm_num
    rw [h2] at han
    apply congr_arg (fun x => (2^(n+1))⁻¹*x) at han
    simp at han
    rw [han]
    calc  (2 ^ (n + 1))⁻¹ * (8 / 5 * (2 ^ n * b n) + 6 / 5 * (2 ^ n * √(1 - b n ^ 2)))
    _ = (2 ^ (n + 1))⁻¹ * 2^(n+1) * (4/5 * (b n) + 3/5 * √(1 - b n ^ 2)) := by ring_nf
    _ = 4/5 * (b n) + 3/5 * √(1 - b n ^ 2) := by norm_num

  -- now let's compute b
  have hb0: b 0 = 0 := by
    rw [← ha0, def_b]; simp
  simp_rw [def_b]
  -- now we recurse while simplifying
  norm_cast at h
  have hb1: b 1 = 3 / 5 := by
    rw [h 0, hb0]; norm_num
  have hb2: b 2 = 24 / 25 := by
    rw [h 1, hb1]; norm_num;
    convert_to 12 / 25 + 3 / 5 * (√(4^2) / √(5^2)) = 24 / 25; norm_num
    simp; norm_num
  have hb3: b 3 = 117 / 125 := by
    rw [h 2, hb2]; norm_num;
    convert_to 96/125 + 3 / 5 * (√(7^2) / √(25^2)) = 117 / 125; norm_num
    simp; norm_num
  have hb4: b 4 = 24 / 25 := by
    rw [h 3, hb3]; norm_num;
    convert_to 468 / 625 + 3 / 5 * (√(44^2) / √(125^2)) = 24 / 25; norm_num
    simp; norm_num
  have hb5: b 5 = 117 / 125 := by
    rw [h 4, hb4]; norm_num;
    convert_to 96/125 + 3 / 5 * (√(7^2) / √(25^2)) = 117 / 125; norm_num
    simp; norm_num
  have hb6: b 6 = 24 / 25 := by
    rw [h 5, hb5]; norm_num;
    convert_to 468 / 625 + 3 / 5 * (√(44^2) / √(125^2)) = 24 / 25; norm_num
    simp; norm_num
  have hb7: b 7 = 117 / 125 := by
    rw [h 6, hb6]; norm_num;
    convert_to 96/125 + 3 / 5 * (√(7^2) / √(25^2)) = 117 / 125; norm_num
    simp; norm_num
  have hb8: b 8 = 24 / 25 := by
    rw [h 7, hb7]; norm_num;
    convert_to 468 / 625 + 3 / 5 * (√(44^2) / √(125^2)) = 24 / 25; norm_num
    simp; norm_num
  have hb9: b 9 = 117 / 125 := by
    rw [h 8, hb8]; norm_num;
    convert_to 96/125 + 3 / 5 * (√(7^2) / √(25^2)) = 117 / 125; norm_num
    simp; norm_num
  have hb10: b 10 = 24 / 25 := by
    rw [h 9, hb9]; norm_num;
    convert_to 468 / 625 + 3 / 5 * (√(44^2) / √(125^2)) = 24 / 25; norm_num
    simp; norm_num
  -- substituting hb10 into goal gives the answer
  rw [hb10]; norm_num