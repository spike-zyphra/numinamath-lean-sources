import Mathlib

/- 11. Let the sequence of positive numbers $a_{0}, a_{1}, a_{2}, \cdots$ satisfy $a_{0}=a_{1}=1$ and $\sqrt{a_{n} a_{n-2}}-\sqrt{a_{n-1} a_{n-2}}=2 a_{n-1}, n=2,3, \cdots$, find the general term formula of this sequence. -/
theorem algebra_230932 (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h0 : a 0 = 1) (h1 : a 1 = 1)
    (h : ∀ n ≥ 2, Real.sqrt (a n * a (n - 2)) - Real.sqrt (a (n - 1) * a (n - 2)) = 2 * a (n - 1)) :
    ∀ n, a n = ∏ k ∈ Finset.Icc 1 n, (2 ^ k - 1) ^ 2 := by
  -- let's factor out √a_n from the recursive relation
  have h0': ∀n≥2, √(a n) = √(a (n-1)) + 2 * (a (n-1))/√(a (n-2)) := by
    intro n hn
    specialize h n hn
    apply congr_arg (fun x => (x + √(a (n - 1) * a (n - 2)))/ √(a (n-2))) at h
    convert_to (√(a n * a (n - 2)) - √(a (n - 1) * a (n - 2)) + √(a (n - 1) * a (n - 2))) / √(a (n - 2)) = (2 * a (n - 1) + √(a (n - 1) * a (n - 2))) / √(a (n - 2))
    · apply Eq.symm
      calc (√(a n * a (n - 2)) - √(a (n - 1) * a (n - 2)) + √(a (n - 1) * a (n - 2))) / √(a (n - 2))
      _ = √(a n * a (n - 2))/ √(a (n - 2)) := by ring_nf
      _ = √(a n) * √ (a (n - 2))/ √(a (n - 2)) := by rw [Real.sqrt_mul (by linarith [ha n])];
      _ = √(a n) := by rw [mul_div_assoc, div_self (by exact Real.sqrt_ne_zero'.mpr (ha (n - 2))), mul_one];
    · apply Eq.symm
      calc (2 * a (n - 1) + √(a (n - 1) * a (n - 2))) / √(a (n - 2))
      _ = 2 * a (n - 1) / √(a (n - 2)) + √(a (n - 1) * a (n - 2)) / √(a (n - 2)) := by ring_nf
      _ = 2 * a (n - 1) / √(a (n - 2)) + √(a (n - 1)) * √(a (n - 2)) / √(a (n - 2)) := by rw [Real.sqrt_mul (by linarith [ha (n - 1)])]
      _ = 2 * a (n - 1) / √(a (n - 2)) + √(a (n - 1)) * (√(a (n - 2)) / √(a (n - 2))) := by ring_nf
      _ = √(a (n - 1)) + 2 * a (n - 1) / √(a (n - 2)) := by rw [div_self (by exact Real.sqrt_ne_zero'.mpr (ha (n-2)))]; ring_nf;
    · exact h
  -- now we can define a sequence b_n = √(a_(n+1)/a_n)
  let q:∃ b:ℕ → ℝ, b = fun n => √(a (n+1)/a n) := by
    use fun n => √(a (n + 1) / a n)
  obtain ⟨b, bdef⟩ := q
  -- we can compute that b_0 = 1
  have hb0: b 0 = 1 := by
    calc b 0
      _ = √(a 1 / a 0) := by rw [bdef]
      _ = √(1/1) := by rw [h0, h1]
      _ = 1 := by norm_num
  -- we can then obtain a recursion relation for b_n
  have hbn: ∀ n≥1, b n = 1 + 2 * b (n-1) := by
    intro n hn
    rw [bdef]; simp
    have hn': n-1+1=n := by omega
    rw [hn']
    specialize h0' (n+1) (by linarith)
    rw [Real.sqrt_div (by linarith [ha (n+1)]), h0']
    simp
    calc (√(a n) + 2 * a n / √(a (n - 1))) / √(a n)
    _ = √(a n)/ √(a n) + 2 * (a n / √(a n)) / √(a (n - 1)) := by ring_nf
    _ = 1 + 2 * √(a n) / √(a (n - 1)) := by rw [div_self (by exact Real.sqrt_ne_zero'.mpr (ha n)), Real.div_sqrt]
    _ = 1 + 2 * √(a n / a (n - 1)) := by rw [mul_div_assoc, ← Real.sqrt_div (by linarith [ha n])]
  -- it's then obvious that b_n = 2^(n+1)-1
  have hbn': ∀ n, b n = 2^(n+1) - 1 := by
    intro n
    induction n with
    | zero => rw [hb0]; norm_num
    | succ n ih =>
      calc b (n + 1)
      _ = 1 + 2 * b n := by rw [hbn (n+1) (by simp), Nat.add_sub_assoc (by norm_num), Nat.sub_self, Nat.add_zero]
      _ = 1 + 2 * (2^(n+1) - 1) := by rw [ih]
      _ = 2^(n+1+1) - 1 := by ring_nf
  -- now we relate that to a_n
  rw [bdef] at hbn'; simp at hbn'
  -- the goal is then a simple induction
  intro n
  induction n with
  | zero => simp; assumption
  | succ n' ih =>
    -- move to Ico for nicer handling
    have hicc:∀ a b:ℕ, Finset.Icc a b = Finset.Ico a (b+1) := by
      intro a b
      ext c; simp; omega
    rw [hicc] at ih ⊢
    rw [Finset.prod_Ico_succ_top (by omega), ← ih]
    specialize hbn' n'
    apply congr_arg (fun x => x ^ 2) at hbn'
    rw [← hbn', Real.sq_sqrt (by apply div_nonneg; linarith [ha (n'+1)]; linarith [ha n']), ← mul_div_assoc, mul_comm, mul_div_assoc, div_self (by linarith [ha n']), mul_one]