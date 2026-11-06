import Mathlib

/- 8. 44 Let the sequence $\left\{a_{n}\right\}$ satisfy:

$$

a_{1}=1, a_{n+1}=\frac{a_{n}}{2}+\frac{1}{4 a_{n}}, n=1,2, \cdots

$$


Prove: When $n>1$, $\sqrt{\frac{2}{2 a_{n}^{2}-1}}$ is a natural number. -/

theorem algebra_255385 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = a n / 2 + 1 / (4 * a n)) :
    ∀ n > 1, ∃ m : ℕ, m ^ 2 = 2 / (2 * (a n) ^ 2 - 1) := by
    -- to be able to divide and mulitply by a n, we first show that a n is positive
  have hl0: ∀n≥1, 0 < a n := by
    intro n hn
    induction n, hn using Nat.le_induction
    case base => rw [ha1]; exact zero_lt_one
    case succ n' hmn hn =>
      rw [han]
      apply add_pos
      linarith
      apply div_pos
      norm_num; linarith; linarith;
  -- then show that √2 /2 < a n
  have h0: ∀n≥1, √2 / 2 <  a n := by
    intro n hn
    induction n, hn using Nat.le_induction
    case base =>
      rw [ha1];
      conv_rhs =>
        calc (1:ℝ)
        _ = 2 / 2 := by ring_nf
      apply mul_lt_mul_of_pos_right (by refine (Real.sqrt_lt' ?_).mpr ?_; norm_num; norm_num)
      simp
    case succ n' hmn hn =>
      rw [han n' (by linarith)]
      apply lt_of_mul_lt_mul_right (a:=4*a n'); ring_nf; rw[mul_inv_cancel₀ (by linarith [hl0 n' (by linarith)])]
      apply lt_of_add_lt_add_right (a:=-√2 * a n' * 2); ring_nf;
      -- complete the square
      have :1 - √2 * a n' * 2 + a n' ^ 2 * 2 = (√2 * a n' - 1) ^ 2 := by ring_nf; simp; ring_nf;
      rw [this];
      apply Real.lt_sq_of_sqrt_lt
      simp;
      suffices √(1/2) < a n' by
        conv_lhs at this =>
          calc √(1/2)
          _ = 1 / √2 := by field_simp
        conv_rhs at this =>
          calc a n'
          _ = (a n' * √2) / √2 := by field_simp
        have q:= (div_lt_div_iff_of_pos_right (by simp)).mp this
        linarith
      suffices √(1 / 2) ≤ √2 / 2 by
        exact lt_of_le_of_lt this hn
      field_simp
      refine (div_le_div_iff₀ ?_ ?_).mpr ?_
      simp; simp; simp;
      linarith [hl0 n' (by linarith)]
  have h0': ∀n≥1, 1/2 < a n^2 := by
    intro n hn; specialize h0 n hn;
    refine (Real.sqrt_lt' (hl0 n hn)).mp ?_
    suffices √2 / 2 = √(1/2) by rw [← this]; trivial
    field_simp
  -- let's define b_n = √(2/(2 * a n ^ 2 - 1))
  let q:∃ b:ℕ → ℝ, b = fun n => √(2/(2* a n^2 - 1)) := by
    use fun n => √ (2 / (2 * a n ^ 2 - 1))
  obtain ⟨b, bdef⟩ := q
  simp at bdef;
  -- let's show that b n is positive
  have hl1: ∀n≥1, 0 < b n := by
    intro n hn
    rw [bdef]; simp;
    nlinarith [h0' n hn]
  -- for later, it will also be useful to have a_n in terms of b n
  have hab: ∀ n ≥ 1, a n = √(1/(b n)^2+1/2) := by
    intro n hn
    rw [bdef]; simp
    apply Eq.symm
    calc √(((√2 / √(2 * a n ^ 2 - 1)) ^ 2)⁻¹ + 2⁻¹)
    _ =  √(((√2 / √(2 * a n ^ 2 - 1)) ^ (2:ℝ))⁻¹ + 2⁻¹) := by norm_cast
    _ = √((2 / (2 * a n ^ 2 - 1))⁻¹ + 2⁻¹) := by apply congr_arg; apply congr_arg (fun x=> x⁻¹+2⁻¹); rw [Real.div_rpow (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (2 * a n ^ 2 - 1))]; norm_cast; rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by linarith [h0' n hn])]
    _ = √(a n ^ 2) := by simp; ring_nf
    _ = a n := by rw [Real.sqrt_sq (by linarith [hl0 n hn])]

  -- now we show a recursive relation for b n
  have h1: ∀n≥3, (b n) = 2 * (b (n-1))*((b (n-2))^2 +1) := by
    intro n hn
    -- we start with a one step recursion
    have hbn: ∀ n≥2, b n = 2 * √(1 + (b (n-1))^2 / 2) * b (n-1) := by
      intro n hn
      calc b n
      _ = √2 / √(2 * a n ^ 2 - 1) := by rw [bdef]
      _ = √2 / √(2 * (a (n-1)/2 + 1/ (4* a (n-1))) ^ 2 - 1) := by
        have hnp:n-1+1=n:= by omega;
        have :=han (n-1) (by omega); rw [hnp] at this; rw [this]
      _ = √2 / √(2 * (a (n-1)/2 - 1/ (4* a (n-1))) ^ 2) := by apply congr_arg; apply congr_arg; ring_nf; rw [mul_inv_cancel₀ (by apply ne_of_gt; exact hl0 _ (by omega))]; ring_nf;
      _ = √2 / (√2 * (a (n-1)/2 - 1/ (4* a (n-1)))) := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by apply le_of_mul_le_mul_right (a:=2*a (n-1)); ring_nf; rw [mul_inv_cancel₀]; simp; linarith [h0' (n-1) (by omega)]; apply ne_of_gt; exact hl0 _ (by omega); linarith [hl0 (n-1) (by omega)])];
      _ = 1 / ((a (n-1)/2 - 1/(4* a (n-1)))) := by rw [← div_div, div_self (by refine (Real.sqrt_ne_zero ?_).mpr ?_; norm_num; norm_num)];
      _ = 1 / ((a (n-1)/2*(2*a (n-1)/ (2*a (n-1))) - 1/(4 * a (n-1)))) := by rw [div_self (by apply ne_of_gt; linarith [hl0 (n-1) (by omega)])]; ring_nf
      _ = 1 /  ((2*a (n-1)^2 -1 )/ (4 * a (n-1))) := by ring_nf
      _ = 4 * a (n-1) / (2 * a (n-1)^2 - 1) := by rw [div_div_eq_mul_div, one_mul]
      _ = 2 * (2 / (2 * a (n-1)^2 - 1)) * a (n-1) := by ring_nf
      _ = 2 * a (n-1) * b (n-1)^2 := by rw [bdef]; simp; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring_nf; apply congr_arg (fun x=>(a (n - 1))*x*4); rw [← Real.sqrt_inv, Real.sq_sqrt (by simp; linarith [h0' (n-1) (by omega)])];
      _ = 2 * √(1 / b (n-1) ^ 2 + 1 / 2) * b (n-1)^2 := by rw [hab (n-1) (by omega)]
      _ = 2 * √((b (n-1))^2) * √(1 / b (n-1) ^ 2 + 1 / 2) * b (n-1) := by rw [Real.sqrt_sq (by linarith [hl1 (n-1) (by omega)])]; ring_nf
      _ = 2 * √((b (n-1))^2 * (1 / b (n-1) ^ 2 + 1 / 2)) * b (n-1) := by rw [Real.sqrt_mul (by nlinarith)]; ring_nf
      _ = 2 * √((b (n-1))^2 / b (n-1) ^ 2 + (b (n-1))^2 / 2) * b (n-1) := by ring_nf
      _ = 2 * √(1 + (b (n-1))^2 / 2) * b (n-1) := by rw [div_self (by apply ne_of_gt; nlinarith [hl1 (n-1) (by omega)];)]
    -- and extend into two step
    calc b n
    _ = 2 * √(1 + b (n - 1) ^ 2 / 2) * b (n - 1) := by rw [hbn n (by omega)]
    _ = 2 * √(1 + (2 * √(1 + b (n - 2) ^ 2 / 2) * b (n - 2)) ^ 2 / 2) * b (n - 1) := by rw [hbn (n-1) (by omega)]; apply congr_arg; apply congr_arg; simp
    _ = 2 * √(1 + (2 * √(1 + b (n - 2) ^ 2 / 2) * b (n - 2)) ^ (2:ℝ) / 2) * b (n - 1) := by norm_cast
    _ = 2 * √(1 + 2^2 * √(1 + b (n - 2) ^ 2 / 2)^2 * b (n - 2) ^ 2 / 2) * b (n - 1) := by rw [Real.mul_rpow (by norm_num) (by nlinarith [hl1 (n-2) (by omega)]), Real.mul_rpow (by norm_num) (by simp)]; norm_cast
    _ = 2 * √(1 + 2 * (1 + b (n - 2) ^ 2 / 2) * b (n - 2) ^ 2) * b (n - 1) := by rw [Real.sq_sqrt (by nlinarith)]; ring_nf
    _ = 2 * √(1 + 2 * b (n-2) ^ 2 + b (n-2) ^ 4) * b (n - 1) := by ring_nf
    _ = 2 * √((1 + b (n-2) ^ 2)^2) * b (n - 1) := by ring_nf
    _ = 2 * (1 + b (n-2) ^ 2) * b (n - 1) := by rw [Real.sqrt_sq (by nlinarith)];
    _ = 2 * (b (n-1))*((b (n-2))^2 +1) := by ring_nf
  -- so it's enough to show that b 3 is a natural number
  suffices ∀ n ≥ 4, ∃ m:ℕ, ↑m ^ 2 = 2 / (2 * a n ^ 2 - 1) by
    intro n hn
    match n with
    | 0 => linarith
    | 1 => linarith
    | 2 => rw [han 1 (by linarith), ha1]; simp; use 4; norm_num
    | 3 => rw [han 2 (by linarith), han 1 (by linarith), ha1]; simp; use 24; norm_num
    | n'+4 => exact this (n'+4) (by linarith)
  -- we show that b n is a natural number for n ≥ 3
  have q:∀ n≥3, ∃m:ℕ, b n = m := by
    intro n hn
    induction n, hn using Nat.twoStepInduction
    case zero =>
      linarith
    case one => linarith

    case more m ih ih2 =>
      match m with
      | 0 => linarith
      | 1 =>
        simp
        rw [bdef]; simp; rw [han 2 (by linarith), han 1 (by linarith), ha1]; simp;
        have q:=
          calc √2 / √(2 * ((2⁻¹ + 4⁻¹) / 2 + (2⁻¹ + 4⁻¹)⁻¹ * 4⁻¹) ^ 2 - 1)
          _ = √2 / √(2 * ((1/2 + 1/4) / 2 + (1/2 + 1/4)⁻¹ * 1/4) ^ 2 - 1) := by ring_nf
          _ = √2 / √(2 * (3/8 + 1/3) ^ 2 - 1) := by ring_nf
          _ = √2 / √(2 * (17/24) ^ 2 - 1) := by ring_nf
          _ = √2 / √(2 * (289/576) - 1) := by ring_nf
          _ = √2 / √(289/288 - 1) := by ring_nf
          _ = √2 / √(1/(2*12^2)) := by ring_nf
          _ = 24 := by rw [Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]; ring_nf; simp; norm_num
        rw [q]; use 24; simp
      | 2 =>
        simp
        rw [h1 4 (by norm_num)]; ring_nf; rw (config := {occs := .pos [3]})[bdef]; simp; have q:= han 1 (by linarith); simp at q; rw [q, ha1]; simp;
        have q:=
          calc √2 / √(2 * (2⁻¹ + 4⁻¹) ^ 2 - 1)
          _ = √2 / √(1/(2*2^2)) := by ring_nf
          _ = 4 := by rw [Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]; ring_nf; simp; norm_num
        rw [q]
        specialize ih2 (by norm_num)
        obtain ⟨m, hm⟩ := ih2
        simp at hm
        use m*2+m*32
        rw [hm]; norm_cast; ring_nf
      | m'+3 =>
        ring_nf
        rw [h1 (5+m') (by linarith)]
        specialize ih (by linarith)
        specialize ih2 (by linarith)
        obtain ⟨m, hm⟩ := ih
        obtain ⟨m2, hm2⟩ := ih2
        ring_nf at hm2
        have q:5 + m' - 1 = 4+m' := by omega
        rw [q]
        have q:5 + m' - 2 = m' + 3 := by omega
        rw [q, hm, hm2]
        use  2 * m2 * (↑m ^ 2 + 1); norm_cast

  -- easy finish now
  intro n hn; specialize q n (by linarith)
  obtain ⟨m, hm⟩ := q
  use m; rw [← hm, bdef]; simp
  calc (√2 / √(2 * a n ^ 2 - 1)) ^ 2
  _ = √2^2/ √(2 * a n ^ 2 - 1)^2 := by ring_nf
  _ = 2 / (2 * a n ^ 2 - 1) := by rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by linarith [h0' n (by omega)])]