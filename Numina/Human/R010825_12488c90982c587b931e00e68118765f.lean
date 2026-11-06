import Mathlib

/- a) Show that the equation

$$
\lfloor x\rfloor\left(x^{2}+1\right)=x^{3},
$$

where $\lfloor x\rfloor$ denotes the largest integer not larger than $x$, has exactly one real solution in each interval between consecutive positive integers.

b) Show that none of the positive real solutions of this equation is rational. -/
theorem algebra_604413 (g : ℝ → Prop) (hg : g = fun x : ℝ => ⌊x⌋ * (x^2 + 1) = x^3) :
  (∀ n : ℤ, 0 < n →  ∃! x : ℝ, n < x ∧ x < n + 1 ∧ g x) ∧ ∀ q : ℚ, 0 < q → ¬ g q := by 
    constructor 
    · intro n npos
      simp [hg]
      -- Then the equation becomes
      -- \[
      -- k((k + y)^2 + 1) = (k + y)^3,
      -- \]
      -- which reduces to
      -- \[
      -- y(k + y)^2 = k \text{.}
      -- \]
      have h1 (y : ℝ) : y * (n + y)^2 = n ↔ n * ((n + y)^2 + 1) = (n + y)^3 := by 
          constructor <;> intro h
          · nth_rw 1 [← h]
            calc 
            _ = (y * (n+y)^2 + y) * (n + y)^2 := by nlinarith
            _ = _ := by nth_rw 1 [h, ← pow_one (n + y), ←pow_add]
          · nlinarith 
      let f : ℝ → ℝ := fun y => y * (n + y)^2  
      -- The function \( f(y) = y(k + y)^2 \) is strictly increasing in \([0, \infinity))
      have hf : StrictMonoOn f (Set.Ici 0) := by 
        intro a ha b hb hab 
        simp [f]
        have npos' : (n : ℝ) > 0 := by norm_cast 
        simp at ha hb
        by_cases hcase : 0 < (n + a)^2 
        apply mul_lt_mul (by linarith) _ hcase hb
        apply pow_le_pow_left₀ <;> try nlinarith
        have : (n + a)^2 = 0 := by nlinarith
        simp [this]
        have : 0 < b := by linarith
        positivity
      -- f continuous in  \([0, 1]\) 
      have contf : ContinuousOn f (Set.Icc 0 1) := by 
        simp [f]
        
        apply ContinuousOn.mul
        · rw [←Function.id_def]
          exact Continuous.continuousOn continuous_id
        · have : ContinuousOn (fun (x : ℝ)=> ↑n + x) (Set.Icc 0 1) := by 
            apply ContinuousOn.add 
            simp [continuousOn_const]
            rw [←Function.id_def]
            exact Continuous.continuousOn continuous_id
          exact ContinuousOn.pow this 2
      -- As \( f(0) = 0 \cdot k \), there exists exactly one \( y_0 \in (0, 1) \) such that \( f(y_0) = k \).
      have ⟨y, hy, ypos, ylt1⟩ : ∃ y, f y = n ∧ 0 < y ∧ y < 1 := by
        have f0 : f 0 = 0 := by simp [f]
        have f1 : f 1 = (n + 1)^2 := by simp [f]
        
        have h2 := intermediate_value_Ioo (by simp) contf
        simp [f0, f1] at h2 
        have h3 : (n : ℝ) ∈ Set.Ioo (0 : ℝ) ((n + 1)^2) := by simp; split_ands <;> nlinarith
        obtain ⟨ y, hy⟩ := h2 h3 
        simp at hy
        exact ⟨y, by split_ands <;> simp [hy]⟩ 
      use n + y 
      simp [ypos, ylt1]

      constructor 
      · have : ⌊y⌋ = 0 := by simp; split_ands <;> linarith
        simp [f] at hy
        simp [this, ←h1 y, hy]
      · intro x x1 x2 hx 
        let k := Int.fract x
        have : ⌊x⌋ = n := by simp [Int.floor_eq_iff]; split_ands <;> linarith
        simp [this] at hx 
        have hh : x = n + k := by rw [←Int.floor_add_fract x, this]
        have : f k = n := by 
          rw [hh, ←h1 k] at hx
          simp [f, hx]
        simp [hh]
        exact (StrictMonoOn.eq_iff_eq hf (by simp [k]) (by simp [le_of_lt ypos])).1 (this.trans hy.symm)
        
    · -- b)  Assume that \( x = k + y \) is rational and let \( x = n / d \), where \( n \) and \( d \) are relatively prime positive integers.
      intro q hq fq
      simp [hg] at fq
      -- The previous proof show equation (1) has no positive integral solutions, so the denominator not equal 1.
      have h1 : q.den ≠ 1 := by 
        intro qd1 
        simp [Rat.den_eq_one_iff] at qd1
        rw [← qd1] at fq
        simp [mul_add] at fq
        have : q.num = 0 := by norm_cast at fq; linarith
        simp at this 
        linarith 
      -- The given equation then becomes
      -- \[
      -- \frac{k(n^2 + d^2)}{d^2} = \frac{n^3}{d^3}
      -- \]
      -- or
      -- \[
      -- d k(n^2 + d^2) = n^3 \text{.}
      -- \]
      rw [← Rat.num_div_den q] at fq
      field_simp at fq 
      nth_rw 1 [show 3 = 1 + 2 by rfl, pow_add, ←mul_assoc] at fq 
      simp [ mul_eq_mul_right_iff] at fq 
      -- Since \( x \) is not an integer, \( d \) has at least one prime divisor. It follows from the last equation that this prime divisor also divides \( n \), a contradiction.
      obtain ⟨p, pp, pdvd⟩ := Nat.exists_prime_and_dvd h1 
      have pdvd' : p ∣ q.num.natAbs := by 
        norm_cast at fq 
        have : (p : ℤ) ∣ q.den := by norm_cast 
        exact  Int.Prime.dvd_pow pp <| fq ▸ (dvd_mul_of_dvd_right this _) 
      have := q.reduced 
      have h1 := Nat.dvd_gcd pdvd' pdvd
      rw [Nat.Coprime] at this 
      simp [this] at h1
      simp [h1] at pp
      tauto