import Mathlib

/- Determine the largest real number $a$ such that for all $n \geqslant 1$ and for all real numbers $x_{0}, x_{1}, \ldots,
x_{n}$ satisfying $0=x_{0}'<'x_{1}'<'x_{2}<\cdots'<'x_{n}$, we have  $$ \frac{1}{x_{1}-x_{0}}+\frac{1}{x_{2}-x_{1}}+\cdots+\frac
{1}{x_{n}-x_{n-1}} \geqslant a\left(\frac{2}{x_{1}}+\frac{3}{x_{2}}+\cdots+\frac{n+1}{x_{n}}\right) . $$  Answer. The larg
est $a$ is $\frac{4}{9}$.-/

lemma sum_of_inv_k_mul_kplus2 : ∀ n, ∑ i ∈ Finset.range (n+2), (1/((i:ℝ)+1) - 1/((i:ℝ)+3)) = 3/2 - 1/(n+3) - 1/(n+4) := by
  intro n
  induction n with
  | zero => ring_nf
  | succ k hk =>
    rw [add_assoc]; nth_rw 2 [add_comm]; rw [← add_assoc, Finset.sum_range_succ, hk]; simp
    have temp1 : ((k:ℝ) + 3)⁻¹ = ((k:ℝ) + 2 + 1)⁻¹ := by simp; ring
    have temp2 : ((k:ℝ) + 4)⁻¹ = ((k:ℝ) + 1 + 3)⁻¹ := by simp; ring
    have temp3 : ((k:ℝ) + 2 + 3)⁻¹ = ((k:ℝ) + 1 + 4)⁻¹ := by simp; ring
    rw [temp1, temp2, temp3]; ring

theorem inequalities_24863 (a : ℝ) :
  (∀ n ≥ 1, ∀ x : ℕ → ℝ,
    (StrictMono x ∧ x 0 = 0) →
      ∑ i ∈ Finset.range n, (1 / (x (i + 1) - x i)) ≥ a * ∑ i ∈ Finset.range n, ((i + 2) / (x (i + 1)))) ↔ a ≤ 4 / 9 := by

apply Iff.intro
· intro h
  let x : ℕ → ℝ := fun i => i * (i + 1) * (i + 2)
  have hx : StrictMono x ∧ x 0 = 0 := by
    apply And.intro; intro i j hij; simp [x]; apply mul_lt_mul; apply mul_lt_mul; simp; exact hij
    simp; apply le_of_lt; exact hij; linarith; simp; simp; apply le_of_lt; exact hij; linarith
    apply mul_nonneg_iff.2; left; apply And.intro; simp; linarith; simp [x]
  have x_sub : ∀ i, x (i + 1) - x i = 3 * (i + 1) * (i + 2) := by intro i; simp [x]; ring_nf

  have x_a : ∀ n ≥ 2, ∑ i ∈ Finset.range n, (1 / (x (i + 1) - x i)) ≥ a * ∑ i ∈ Finset.range n, ((i + 2) / (x (i + 1))) := by
    intro n hn; apply h; linarith [hn]; exact hx

  have eq1 : ∀ n ≥ 1, ∑ i ∈ Finset.range n, (1 / (x (i + 1) - x i)) = (1/3) * (1 - 1/(n + 1)) := by
    intro n hn
    calc
      ∑ i ∈ Finset.range n, (1 / (x (i + 1) - x i)) = (1/3) * ∑ i ∈ Finset.range n, (1/((i + 1) : ℝ) - 1/((i + 2) : ℝ)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr; rfl; intro i _; rw [x_sub]
        have pos : 3 * ((i : ℝ) + 1) * ((i : ℝ) + 2) ≠ 0 := by
          apply ne_of_gt; apply mul_pos_iff.2; left; apply And.intro; apply mul_pos_iff.2; left; apply And.intro; norm_num; linarith; linarith
        apply (div_eq_iff pos).2; rw [mul_sub, sub_mul]; simp
        have temp1 : 3⁻¹ * ((i : ℝ) + 1)⁻¹ * (3 * ((i : ℝ) + 1) * ((i : ℝ) + 2)) = i + 2 := by
          rw [← mul_assoc, ← mul_inv, inv_mul_cancel₀]; simp; apply ne_of_gt; apply mul_pos_iff.2; left; apply And.intro; norm_num; linarith
        have temp2 : 3⁻¹ * ((i : ℝ) + 2)⁻¹ * (3 * ((i : ℝ) + 1) * ((i : ℝ) + 2)) = i + 1 := by
          nth_rw 2 [mul_assoc]; nth_rw 4 [mul_comm]; nth_rw 2 [← mul_assoc]; rw [← mul_assoc, ← mul_inv, inv_mul_cancel₀]
          simp; apply ne_of_gt; apply mul_pos_iff.2; left; apply And.intro; norm_num; linarith
        rw [temp1, temp2]; ring_nf
      _ = (1/3) * (1 - 1/(n + 1)) := by
        have m_ex : ∃ m : ℕ, n = 1 + m := by
          apply Nat.exists_eq_add_of_le; exact hn
        obtain ⟨m, hm⟩ := m_ex
        rw [add_comm] at hm
        have temp : ∑ i ∈ Finset.range n, (1/((i + 1) : ℝ) - 1/((i + 2) : ℝ)) = 1 - 1/(n + 1) := by
          simp; rw [hm, Finset.sum_range_succ', Finset.sum_range_succ]
          have temp' : ∑ i ∈ Finset.range m,((((i + 1) : ℕ) : ℝ) + 1)⁻¹ = ∑ i ∈ Finset.range m, ((i : ℝ) + 2)⁻¹ := by
            apply Finset.sum_congr; rfl; intro i _; simp; ring
          rw [temp']; simp; ring
        rw [temp]

  have eq2 : ∀ n ≥ 2, a * ∑ i ∈ Finset.range n, ((i + 2) / (x (i + 1))) = (a/2) * (3/2 - 1/(n + 1) - 1/(n + 2)) := by
    intro n hn
    have m_ex : ∃ m : ℕ, n = 2 + m := by
      apply Nat.exists_eq_add_of_le; exact hn
    obtain ⟨m, hm⟩ := m_ex
    rw [add_comm] at hm
    calc
      a * ∑ i ∈ Finset.range n, ((i + 2) / (x (i + 1))) = (a/2) * ∑ i ∈ Finset.range n, (1/((i:ℝ) + 1) - 1/((i:ℝ) + 3)) := by
        rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr; rfl; intro i _; simp [x]; rw [mul_div]
        have pos : ((i:ℝ) + 1) * ((i:ℝ) + 1 + 1) * ((i:ℝ) + 1 + 2) ≠ 0 := by
          apply ne_of_gt; apply mul_pos_iff.2; left; apply And.intro; apply mul_pos_iff.2; left; apply And.intro; linarith; linarith; linarith
        apply (div_eq_iff pos).2; rw [mul_assoc, sub_mul]
        have temp1 : ((i:ℝ) + 1)⁻¹ * (((i:ℝ) + 1) * ((i:ℝ) + 1 + 1) * ((i:ℝ) + 1 + 2)) = ((i:ℝ) + 2) * ((i:ℝ) + 3) := by
          rw [mul_assoc, ← mul_assoc, inv_mul_cancel₀]; ring_nf; apply ne_of_gt; linarith
        have temp2 :  ((i:ℝ) + 3)⁻¹ * (((i:ℝ) + 1) * ((i:ℝ) + 1 + 1) * ((i:ℝ) + 1 + 2)) = ((i:ℝ) + 2) * ((i:ℝ) + 1) := by
          have temp' : (i:ℝ) + 1 + 2 = (i:ℝ) + 3 := by ring
          rw [temp', mul_comm, mul_assoc, mul_inv_cancel₀]; ring_nf; apply ne_of_gt; linarith
        rw [temp1, temp2]; ring_nf
      _ = (a/2) * (3/2 - 1/(m + 3) - 1/(m + 4)) := by
        apply mul_eq_mul_left_iff.2; left; rw [hm]; apply sum_of_inv_k_mul_kplus2
      _ = (a/2) * (3/2 - 1/(n + 1) - 1/(n + 2)) := by
        apply mul_eq_mul_left_iff.2; left; simp [hm]
        have temp1 : ((m:ℝ) + 3)⁻¹ = ((m:ℝ) + 2 + 1)⁻¹ := by simp; ring
        have temp2 : ((m:ℝ) + 4)⁻¹ = ((m:ℝ) + 2 + 2)⁻¹ := by simp; ring
        rw [temp1, temp2]

  have iq_a : ∀ (n : ℕ), n ≥ 2 → (1/3) * (1 - 1/(n + 1)) ≥ (a/2) * (3/2 - 1/(n + 1) - 1/(n + 2)) := by
    intro n hn
    calc
      (1/3) * (1 - 1/(n + 1)) = ∑ i ∈ Finset.range n, (1 / (x (i + 1) - x i)) := by rw [eq1]; linarith [hn]
      _ ≥ a * ∑ i ∈ Finset.range n, ((i + 2) / (x (i + 1))) := by apply x_a; exact hn
      _ = (a/2) * (3/2 - 1/(n + 1) - 1/(n + 2)) := by apply eq2; exact hn

  by_contra ha; simp at ha
  have ex_m : ∃ m : ℕ, (m : ℝ) > (3 * a)/(9 * a - 4) ∧ m ≥ 2:= by
    have ex_u : ∃ u : ℕ, (u : ℝ) > (3 * a)/(9 * a - 4) := by apply exists_nat_gt
    obtain ⟨u, hu⟩ := ex_u
    set m := u + 2
    refine ⟨m, ?_, ?_⟩
    · simp [m]
      linarith
    · simp [m]
  obtain ⟨m, hm⟩ := ex_m
  have contr1 : 4 * m ≥ a * (9 * m - 3) := by
    calc
      4 * (m:ℝ) = ((m + 1) * (1 - 1/(m + 1))) * 12 * (1/3) := by
        rw [mul_sub]; simp; rw [mul_inv_cancel₀]; ring_nf; apply ne_of_gt; linarith [m]
      _ = ((1/3) * (1 - 1/(m + 1))) * (12 * (m + 1)) := by ring
      _ ≥ ((a/2) * (3/2 - 1/(m + 1) - 1/(m + 2))) * (12 * (m + 1)) := by
        apply mul_le_mul; apply iq_a; exact hm.2; rfl; linarith [m]; apply mul_nonneg_iff.2; left;
        apply And.intro; norm_num; simp; apply inv_le_one; linarith
      _ = a * ((9 - 6/(m + 1) - 6/(m + 2)) * (m + 1)) := by ring_nf
      _ = a * (9 * m + 3 - 6 * ((m + 1)/(m + 2))) := by
        rw [sub_mul, sub_mul, div_mul_cancel₀]; ring_nf; apply ne_of_gt; linarith [m]
      _ ≥ a * (9 * m - 3) := by
        have temp : ((m:ℝ) + 1)/((m:ℝ) + 2) ≤ 1 := by
          have pos : (m:ℝ) + 2 > 0 := by linarith [m]
          apply (div_le_iff₀ pos).2; simp
        nlinarith [a, temp]
  have contr2 : 4 * m < a * (9 * m - 3) := by
    have temp : (9 * a - 4) * m > 3 * a := by
      calc
        (9 * a - 4) * m > (9 * a - 4) * ((3 * a)/(9 * a - 4)) := by
          simp; apply mul_lt_mul'; rfl; exact hm.1; apply mul_nonneg_iff.2; left;
          apply And.intro; linarith [ha]; simp; linarith [ha]; linarith [ha]
        _ = 3 * a := by rw [mul_div_cancel₀]; apply ne_of_gt; linarith [ha]
    linarith [temp]
  nlinarith [contr1, contr2]


· have cauchy_schwarz : ∀ a b c d : ℝ, 0 < a → 0 < b → 0 < c → 0 < d → (a + b) * (c + d) ≥ (√(a * c) + √(b * d))^2 := by
    intro a b c d ha hb hc hd
    have temp : a * d + b * c ≥ 2 * √(a * c) * √(b * d) := by
      calc
        a * d + b * c = (a * d + b * c - 2 * √(a * d) * √(b * c)) + 2 * √(a * d) * √(b * c) := by ring
        _ = (√(a * d) - √(b * c))^2 + 2 * √(a * d) * √(b * c) := by
          rw [pow_two]; ring_nf; rw [pow_two]; rw [pow_two]
          rw [Real.mul_self_sqrt]; rw [Real.mul_self_sqrt]
          nlinarith [hb, hc]; nlinarith [ha, hd]
        _ ≥ 2 * √(a * d) * √(b * c) := by simp; apply pow_two_nonneg
        _ = 2 * √(a * c) * √(b * d) := by
          rw [Real.sqrt_mul]; rw [Real.sqrt_mul]; rw [Real.sqrt_mul]; rw [Real.sqrt_mul]; ring
          linarith [hb]; linarith [ha]; linarith [hb]; linarith [ha]
    rw [pow_two]; ring_nf; rw [pow_two]; rw [pow_two]; rw [Real.mul_self_sqrt]; rw [Real.mul_self_sqrt]
    linarith [temp]; nlinarith [hb, hd]; nlinarith [ha, hc]

  intro ha n hn x hx
  have m_ex : ∃ m : ℕ, n = 1 + m := by
    apply Nat.exists_eq_add_of_le; apply Nat.le_of_lt_succ; simp; exact hn
  obtain ⟨m, hm⟩ := m_ex
  have xk_pos : ∀ k, k > 0 → 0 < x k := by
    intro k hk
    calc
      0 = x 0 := by rw [hx.2]
      _ < x k := by apply hx.1; exact hk

  have iq_1 : ∀ k, ((x (k + 1)) + (x (k + 2) - x (k + 1))) * ((k + 1)^2 / (x (k + 1)) + 9 / (x (k + 2) - x (k + 1))) ≥ (k + 4)^2 := by
    intro k
    let a := x (k + 1)
    let b := x (k + 2) - x (k + 1)
    let c := (k + 1)^2 / (x (k + 1))
    let d := 9 / (x (k + 2) - x (k + 1))
    let u := a * c
    let v := b * d
    have hac : √u = k + 1 := by
      apply Real.sqrt_eq_cases.2; left; apply And.intro
      · have pos : x (k + 1) ≠ 0 := by
          apply ne_of_gt; apply xk_pos; simp
        simp [u, a, c]; nth_rw 2 [mul_comm]; simp [pos]; ring
      · linarith
    have hbd : √v = 3 := by
      apply Real.sqrt_eq_cases.2; left; apply And.intro
      · have pos : x (k + 2) - x (k + 1) ≠ 0 := by apply ne_of_gt; simp; apply hx.1; simp
        simp [v, b ,d]; nth_rw 2 [mul_comm]; simp [pos]; norm_num
      · norm_num
    calc
      ((x (k + 1)) + (x (k + 2) - x (k + 1))) * ((k + 1)^2 / (x (k + 1)) + 9 / (x (k + 2) - x (k + 1))) = (a + b) * (c + d) := by simp [a, b, c, d]
      _ ≥ (√(a * c) + √(b * d))^2 := by
        apply cauchy_schwarz
        · simp [a]
          apply xk_pos; simp
        · simp [b]; apply hx.1; simp
        · simp [c]; apply div_pos_iff.2; left; apply And.intro
          · rw [pow_two]; ring_nf; nlinarith [k]
          · apply xk_pos; simp
        · simp [d]; apply hx.1; simp
      _ = (k + 1 + 3)^2 := by rw [← hac, ← hbd]
      _ = (k + 4)^2 := by ring

  have iq_2 : ∀ k, 9 / (x (k + 2) - x (k + 1)) ≥ (k + 4)^2 / x (k + 2) - (k + 1)^2 / x (k + 1) := by
    intro k
    have temp1 : ((x (k + 1)) + (x (k + 2) - x (k + 1))) * ((k + 1)^2 / (x (k + 1)) + 9 / (x (k + 2) - x (k + 1))) ≥ (k + 4)^2 := by apply iq_1
    simp at temp1
    have pos : 0 < x (k + 2) := by apply xk_pos; linarith [k]
    have temp2 : (k + 4)^2 / x (k + 2) ≤ (k + 1)^2 / (x (k + 1)) + 9 / (x (k + 2) - x (k + 1)) := by apply (div_le_iff₀' pos).2 temp1
    linarith [temp2]

  have iq3 : 9 * ∑ i ∈ Finset.range n, (1 / (x (i + 1) - x i)) ≥ 4 * ∑ i ∈ Finset.range n, ((i + 2) / (x (i + 1))) := by
    calc
      9 * ∑ i ∈ Finset.range n, (1 / (x (i + 1) - x i)) = ∑ i ∈ Finset.range (m + 1), (9 / (x (i + 1) - x i)) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr; rw [hm, add_comm]; intro i _; ring_nf
      _ = (∑ i ∈ Finset.range m, (9 / (x (i + 2) - x (i + 1)))) + 9 / (x 1 - x 0) := by rw [Finset.sum_range_succ']
      _ ≥ (∑ i ∈ Finset.range m, ((i + 4)^2 / x (i + 2) - (i + 1)^2 / (x (i + 1)))) + 9 / (x 1 - x 0) := by
        have temp : ∑ i ∈ Finset.range m, (9 / (x (i + 2) - x (i + 1))) ≥ ∑ i ∈ Finset.range m, ((i + 4)^2 / x (i + 2) - (i + 1)^2 / (x (i + 1))) := by
          apply Finset.sum_le_sum; intro i hi; apply iq_2
        linarith [temp]
      _ = ∑ i ∈ Finset.range m, (i + 4)^2 / x (i + 2) - ∑ i ∈ Finset.range m, (i + 1)^2 / (x (i + 1)) + 9 / x 1 := by rw [hx.2]; simp
      _ ≥ 4 * ∑ i ∈ Finset.range n, ((i + 2) / (x (i + 1))) := by
        cases m with
        | zero =>
          rw [hm]; simp; rw [mul_div]; norm_num
          have pos : 1 / x 1 > 0 := by apply div_pos_iff.2; left; apply And.intro; simp; apply xk_pos; simp
          have pos' : x 1 ≠ 0 := by apply ne_of_gt; apply xk_pos; simp
          calc
            8 / x 1 ≤ 1 / x 1 + 8 / x 1 := by linarith [pos]
            _ = 9 / x 1 := by rw [div_add_div_same]; ring
        | succ l =>
          have temp1 : ∑ i ∈ Finset.range (l + 1), (i + 4) ^ 2 / x (i + 2) ≥ ∑ i ∈ Finset.range l, (i + 4) ^ 2 / x (i + 2) + 4 * (l + 3) / (x (l + 2)):= by
            rw [Finset.sum_range_succ]; simp
            have pos : 0 < x (l + 2) := by apply xk_pos; simp
            apply (div_le_iff₀' pos).2; rw [mul_div_cancel₀]; ring_nf
            calc
              12 + (l : ℝ) * 4 ≤ 16 + (l : ℝ) * 8 := by linarith
              _ ≤ 16 + (l : ℝ) * 8 + (l : ℝ)^2 := by simp
            apply ne_of_gt; exact pos
          have temp2 : ∑ i ∈ Finset.range (l + 1), (i + 1)^2 / (x (i + 1)) = ∑ i ∈ Finset.range l, (i + 2)^2 / (x (i + 2)) + 1 / (x 1) := by
            rw [Finset.sum_range_succ']; simp; apply Finset.sum_congr; rfl; intro i _; ring_nf
          have temp3 : ∑ i ∈ Finset.range l, (i + 2)^2 / (x (i + 2)) + 4 * ∑ i ∈ Finset.range l, (i + 3) / x (i + 2)
          = ∑ i ∈ Finset.range l, (i + 4)^2 / (x (i + 2)) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr; rfl; intro i _; ring
          have temp4 : (9 / x 1) + 4 * ∑ i ∈ Finset.range l, (i + 3) / x (i + 2) - 1 / x 1 = 4 * ∑ i ∈ Finset.range (l + 1), (i + 2) / x (i + 1) := by
            calc
              (9 / x 1) + 4 * ∑ i ∈ Finset.range l, (i + 3) / x (i + 2) - 1 / x 1 = 4 * (∑ i ∈ Finset.range l, (i + 3) / x (i + 2) + 2 / x 1) := by ring
              _ = 4 * (∑ i ∈ Finset.range (l + 1), (i + 2) / x (i + 1)) := by
                rw [Finset.sum_range_succ']; simp; apply Finset.sum_congr; rfl; intro i _; ring_nf
          have temp5 : 4 * ∑ i ∈ Finset.range (l + 1), (i + 2) / x (i + 1) + 4 * (l + 3) / (x (l + 2))
          = 4 * ∑ i ∈ Finset.range (l + 1 + 1), (↑i + 2) / x (i + 1) := by
            nth_rw 2 [Finset.sum_range_succ]; ring_nf; nth_rw 2 [mul_add]; simp
            have pos : x (2 + l) ≠ 0 := by apply ne_of_gt; apply xk_pos; simp
            apply (div_eq_iff pos).2; rw [mul_assoc, div_mul_cancel₀]; ring; exact pos
          rw [hm]; nth_rw 4 [add_comm]; nlinarith [temp1, temp2, temp3, temp4, temp5]

  calc
    ∑ i ∈ Finset.range n, 1 / (x (i + 1) - x i) = (1/9) * (9 * ∑ i ∈ Finset.range n, 1 / (x (i + 1) - x i)) := by rw [← mul_assoc]; simp
    _ ≥ (1/9) * (4 * ∑ i ∈ Finset.range n, ((i + 2) / (x (i + 1)))) := by linarith [iq3]
    _ = (4/9) * ∑ i ∈ Finset.range n, ((i + 2) / (x (i + 1))) := by ring
    _ ≥ a * ∑ i ∈ Finset.range n, ((i + 2) / (x (i + 1))) := by
      apply mul_le_mul; exact ha; apply le_of_eq; rfl; apply Finset.sum_nonneg; intro i _; apply div_nonneg_iff.2;
      left; apply And.intro; linarith [i]; apply le_of_lt; apply xk_pos; linarith [i]; norm_num
