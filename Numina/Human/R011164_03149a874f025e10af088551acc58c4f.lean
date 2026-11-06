import Mathlib
/-- For each ordered pair of real numbers $(x,y)$ satisfying\[\log_2(2x+y) = \log_4(x^2+xy+7y^2)\]there is a real number $K$ such that\[\log_3(3x+y) = \log_9(3x^2+4xy+Ky^2).\]Find the product of all possible values of $K$. -/
theorem algebra_97521 : ∏ᶠ k ∈ {k : ℝ | ∃ (x y : ℝ), 0 < 2 * x + y ∧ 0 < x^2 + x * y + 7 * y^2 ∧ 0 < 3 * x + y ∧ 0 < 3 * x^2 + 4 * x * y + k * y^2 ∧ Real.logb 2 (2 * x + y) = Real.logb 4 (x^2 + x * y + 7 * y^2) ∧ Real.logb 3 (3 * x + y) = Real.logb 9 (3 * x^2 + 4 * x * y + k * y^2)}, k = 189 := by
  have em : {k : ℝ | ∃ (x y : ℝ), 0 < 2 * x + y ∧ 0 < x^2 + x * y + 7 * y^2 ∧ 0 < 3 * x + y ∧ 0 < 3 * x^2 + 4 * x * y + k * y^2 ∧ Real.logb 2 (2 * x + y) = Real.logb 4 (x^2 + x * y + 7 * y^2) ∧ Real.logb 3 (3 * x + y) = Real.logb 9 (3 * x^2 + 4 * x * y + k * y^2)} = (↑{9, 21} : Finset ℝ) := by
    ext k
    simp only [Set.mem_setOf_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor <;> intro h
    · obtain ⟨x, y, d1, d2, d3, d4, g, h⟩ := h
      have alw (a b : ℝ) (h1 : 0 < a) (h2 : 0 < b) : Real.logb a b = Real.logb (a * a) (b * b) := by
        rw [Real.logb_mul (by linarith) (by linarith)]
        have stb : Real.logb (a * a) b = Real.logb a b / 2 := by
          simp only [←Real.log_div_log]
          rw [Real.log_mul (by linarith) (by linarith)]
          ring_nf
        rw [stb]
        ring
      -- change of base
      rw [alw 2 _ (by norm_num) (by assumption)] at g
      rw [alw 3 _ (by norm_num) (by assumption)] at h
      norm_num at g h
      apply_fun (fun x => (4 : ℝ)^x) at g
      apply_fun (fun x => (9 : ℝ)^x) at h
      rw [Real.rpow_logb (by norm_num) (by norm_num) (Left.mul_pos d1 d1), Real.rpow_logb (by norm_num) (by norm_num) d2] at g
      rw [Real.rpow_logb (by norm_num) (by norm_num) (Left.mul_pos d3 d3), Real.rpow_logb (by norm_num) (by norm_num) d4] at h
      -- now we factor into \[(x+2y)(x-y)=0\]
      have ale : (x + 2 * y) * (x - y) = 0 := by ring_nf; ring_nf at g; linarith
      rw [mul_eq_zero] at ale
      -- conclude 2 possible values are 9 and 21
      obtain td | td := ale
      · have wl : x = -2 * y := by clear * - td; linarith
        subst x
        ring_nf at h
        right; nlinarith
      · have wl : x = y := by clear * - td; linarith
        subst x
        ring_nf at h
        left; nlinarith
    -- provide witnesses
    · obtain rfl | rfl := h
      -- witness 1
      · exists 1, 1; norm_num
        have st1 : Real.logb 4 9 = 2 * Real.logb 4 3 := by
          rw [(by norm_num : 9 = (3 : ℝ) * (3 : ℝ))]
          rw [Real.logb_mul (by norm_num) (by norm_num)]
          ring
        rw [st1]
        have st2 : Real.logb 9 16 = 2 * Real.logb 9 4 := by
          rw [(by norm_num : 16 = (4 : ℝ) * (4 : ℝ))]
          rw [Real.logb_mul (by norm_num) (by norm_num)]
          ring
        rw [st2]
        have st3 : Real.logb 4 3 = (Real.logb 2 3) / 2 := by
          simp only [←Real.log_div_log]
          rw [(by norm_num : 4 = (2 : ℝ) * (2 : ℝ)), Real.log_mul (by norm_num) (by norm_num)]
          ring
        rw [st3]
        have st4 : Real.logb 9 4 = (Real.logb 3 4) / 2 := by
          simp only [←Real.log_div_log]
          rw [(by norm_num : 9 = (3 : ℝ) * (3 : ℝ)), Real.log_mul (by norm_num) (by norm_num)]
          ring
        rw [st4]
        ring_nf; exact ⟨by trivial, by trivial⟩
      -- witness 2
      · exists 2, -1; norm_num
        have st1 : Real.logb 4 9 = 2 * Real.logb 4 3 := by
          rw [(by norm_num : 9 = (3 : ℝ) * (3 : ℝ))]
          rw [Real.logb_mul (by norm_num) (by norm_num)]
          ring
        rw [st1]
        have st2 : Real.logb 9 25 = 2 * Real.logb 9 5 := by
          rw [(by norm_num : 25 = (5 : ℝ) * (5 : ℝ))]
          rw [Real.logb_mul (by norm_num) (by norm_num)]
          ring
        rw [st2]
        have st3 : Real.logb 4 3 = (Real.logb 2 3) / 2 := by
          simp only [←Real.log_div_log]
          rw [(by norm_num : 4 = (2 : ℝ) * (2 : ℝ)), Real.log_mul (by norm_num) (by norm_num)]
          ring
        rw [st3]
        have st4 : Real.logb 9 5 = (Real.logb 3 5) / 2 := by
          simp only [←Real.log_div_log]
          rw [(by norm_num : 9 = (3 : ℝ) * (3 : ℝ)), Real.log_mul (by norm_num) (by norm_num)]
          ring
        rw [st4]
        ring_nf; exact ⟨by trivial, by trivial⟩
  simp_rw [em, finprod_mem_coe_finset]
  simp only [Finset.mem_singleton, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, not_false_eq_true,
    Finset.prod_insert, Finset.prod_singleton]
  norm_num