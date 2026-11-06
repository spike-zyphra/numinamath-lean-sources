import Mathlib

/- Let $\mathbb{R}$ be the set of real numbers. Does there exist a function $f: \mathbb{R} \rightarrow \mathbb{R}$ that simultaneously satisfies the following three conditions?
 (a) There is a positive number $M$ such that $-M \leq f(x) \leq M$ for all $x$. (b) $f(1)=1$. (c) If $x \neq 0$, then  $$ f\left(x+\frac{1}{x^{2}}\right)=f(x)+\left[f\left(\frac{1}{x}\right)\right]^{2} $$ -/
theorem algebra_24647 : ¬∃ f : ℝ → ℝ, (∃ M : ℝ, 0 < M ∧ ∀ x, -M ≤ f x ∧ f x ≤ M) ∧ f 1 = 1 ∧ ∀ x ≠ 0, f (x + 1 / x ^ 2) = f x + (f (1 / x)) ^ 2 := by
  -- Assume that $f$ exists and let $n$ be the least integer such that $f(x) \leq \frac{n}{4}$ for all $x$.
  by_contra!
  rcases this with ⟨f, ⟨hM,⟨hf1,hf2⟩⟩⟩
  rcases hM with ⟨M,⟨hM1,hM2⟩⟩
  have hn : ∃ (n : ℤ), (∀ x>0,f x ≤ n / 4) ∧ ∀ (z : ℤ), (∀ x>0,f x ≤ z / 4) → n ≤ z := by
    apply Int.exists_least_of_bdd
    · use 4 ;intro z hz ;specialize hz 1
      rw [hf1] at hz ;simp at hz
      apply (one_le_div (by simp)).mp at hz
      have : (4 : ℝ) = ↑ (4:ℤ) := rfl
      rw [this] at hz ;apply Int.cast_le.mp at hz ;exact hz
    use 4 * (Int.ceil M) ;intro x ;specialize hM2 x
    have : M ≤ ↑(4 * ⌈M⌉) / 4 := by simp ;exact Int.le_ceil M
    intro hx ;linarith
  rcases hn with ⟨n,⟨hn1,hn2⟩⟩
  -- Since $f(2)=2$, we have $n \geq 8$.
  have hf2eq : f 2 = 2 := by
    specialize hf2 1 (by simp) ;simp [hf1,one_add_one_eq_two] at hf2 ;exact hf2
  have h8len : 8 ≤ n := by
    specialize hn1 2 ;rw [hf2eq] at hn1 ;simp at hn1 ;apply (le_div_iff₀ (by simp)).mp at hn1
    ring_nf at hn1 ;apply Int.cast_le.mp at hn1 ;simp at hn1 ;exact hn1
  -- Let $f(x)&gt;\frac{n-1}{4}$.
  have hfxgt : ∃ x>0, f x > ↑(n-1) / 4 := by
    by_contra! h
    specialize hn2 (n -1)
    apply hn2 at h ;linarith
  rcases hfxgt with ⟨x,⟨hx1,hx2⟩⟩
  -- Then $f(1 / x)^2=f\left(x+1 / x^{2}\right)-f(x)&lt;1 / 4$,
  have hfx1 : f (1 / x) ^ 2 = f (x + 1 / x ^ 2) - f x := by specialize hf2 x (by linarith) ;linarith
  have hfx1lt : f (1 / x) ^ 2 < (1 / 2) ^ 2 := by
    have : (1 : ℝ) = ↑ n - ↑ (n - 1) := by simp
    ring_nf ;ring_nf at hfx1 ;rw [this,hfx1,sub_div]
    refine sub_lt_sub_iff.mpr ?_ ;apply add_lt_add_of_le_of_lt
    apply hn1
    have : x⁻¹ ^ 2 > 0 := by simp [hx1]
    linarith ;linarith
  apply abs_lt_of_sq_lt_sq' at hfx1lt
  norm_num at hfx1lt
  -- On the other hand, this implies $\left(\frac{n-1}{4}\right)^{2}&lt;f(x)^{2}=f\left(1 / x+x^{2}\right)-f(1 / x)&lt;\frac{n}{4}+\frac{1}{2}$,
  have h1 : (↑(n - 1) / 4) ^ 2 < (f x) ^ 2 := by
    have : 0 ≤ ↑(n - 1) / (4:ℝ) := by
      apply (le_div_iff₀ ?_).mpr ;simp ;rw [← Int.cast_one] ;apply Int.cast_le.mpr ;linarith ;simp
    refine (sq_lt_sq₀ this (by linarith)).mpr hx2
  have h2 : f (1 / x + x ^ 2) - f (1 / x) < n / 4 - (- 1 / 2) := by
    refine sub_lt_sub_iff.mpr ?_ ;apply add_lt_add_of_le_of_lt
    apply hn1
    have : 1 / x > 0 ∧ x ^ 2 > 0 := by simp [pow_two,hx1]
    linarith ;simp ;linarith
  have hfx2 : f x ^ 2 = f (1 / x + x ^ 2) - f (1 / x) := by specialize hf2 (1/x) (by simp ;linarith) ;simp ;simp at hf2 ;linarith
  have : (↑(n - 1) / (4 : ℝ)) ^ 2 - (↑n / 4 - (- 1 / 2)) < 0 := by linarith
  -- which is impossible when $n \geq 8$.
  have this' : (↑(n - 1) / (4 : ℝ)) ^ 2 - (↑n / 4 - (- 1 / 2)) = (↑ n - 7) * (↑ n + 1) * 1 /16 := by simp ;ring
  rw [this'] at this
  have this'': 0 < ↑n - (7:ℝ) := by
    have : (7 : ℝ)  = ↑ (7 : ℤ) := rfl
    simp ;rw [this] ;apply Int.cast_lt.mpr ;linarith
  have this''': 0 < ↑n + (1:ℝ) := by rw [← Int.cast_one,← Int.cast_add,← Int.cast_zero] ;apply Int.cast_lt.mpr ;linarith
  apply (div_lt_iff₀ (by simp)).mp at this ;rw [mul_one,zero_mul] at this
  apply (pos_iff_neg_of_mul_neg this).mp at this''
  linarith