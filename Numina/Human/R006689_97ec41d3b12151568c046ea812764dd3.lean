import Mathlib

/-
Let $\{a_0,a_1,\ldots\}$ and $\{b_0,b_1,\ldots\}$ be two infinite sequences of integers such that 
$(a_{n}-a_{n-1})(a_n-a_{n-2}) +(b_n-b_{n-1})(b_n-b_{n-2})=0$ for all integers $n\geq 2$. 
Let $M$ be a positive integer. Prove that there exists a positive integer $k$ such that $a_{k+M}=a_{k+M^M}$.
-/
theorem number_theory_640181 (a b : ℕ → ℤ) (M : ℕ) (hM : 0 < M)
(hab : ∀ n, 2 ≤ n → (a n - a (n - 1)) * (a n - a (n - 2)) + (b n - b (n - 1)) * (b n - b (n - 2)) = 0) :
  ∃ k, 0 < k ∧ a (k + M) = a (k + M ^ M) := by
  -- Let $x_n = a_n - a_{n-1}$ and $y_n = b_n - b_{n-1}$ for $n \geq 1$.Here for the sake of convenience, they are all one place behind。
  -- Since $a_n$ and $b_n$ are integers, $x_n$ and $y_n$ are also integers.
  let x n := a (n + 1) - a n
  let y n := b (n + 1) - b n
  -- The given equation is $(a_n-a_{n-1})(a_n-a_{n-2}) + (b_n-b_{n-1})(b_n-b_{n-2})=0$ for $n\geq 2$.
  -- We can rewrite $a_n-a_{n-2}$ as $(a_n-a_{n-1})+(a_{n-1}-a_{n-2}) = x_n+x_{n-1}$.\
  -- Similarly, $b_n-b_{n-2} = y_n+y_{n-1}$.
  -- Substituting these into the equation, we get:\
  -- $x_n(x_n+x_{n-1}) + y_n(y_n+y_{n-1}) = 0$ for $n \geq 2$.\
  -- This can be expanded as $x_n^2 + x_n x_{n-1} + y_n^2 + y_n y_{n-1} = 0$.
  have hxy : ∀ n ,1 ≤ n → (x n) ^ 2 + x n * x (n - 1) + (y n) ^ 2 + y n * y (n - 1) = 0:= by
    intro n hn
    specialize hab (n + 1) (by simp [hn])
    rw [← hab]
    simp [x,y,hn] ;ring_nf
  -- Let $V_n = (x_n, y_n)$ be a vector in $\mathbb{Z}^2$. 
  let V n := ![x n, y n]
  -- The equation can be written as:\
  -- $V_n \cdot V_n + V_n \cdot V_{n-1} = 0$.
  have hV : ∀ n,1 ≤ n → V n ⬝ᵥ V n + V n ⬝ᵥ V (n - 1) = 0 := by
    intro n hn
    specialize hxy n hn
    rw [← hxy]
    simp [V] ;ring_nf
  -- Let $S_n = \|V_n\|^2 = x_n^2+y_n^2$. Since $x_n, y_n$ are integers, $S_n$ is a non-negative integer.
  let S n := V n ⬝ᵥ V n
  have hS : ∀ n , 0 ≤ S n := by
    intro n
    simp [S,V]
    rw [← pow_two,← pow_two]
    nlinarith
  -- The equation becomes $S_n + V_n \cdot V_{n-1} = 0$, or $S_n = -V_n \cdot V_{n-1}$.
  have hS1 : ∀ n,1 ≤ n  → S n = - (V n) ⬝ᵥ (V (n - 1)) := by
    intro n hn
    simp [S]
    specialize hV n hn
    simp at hV
    linarith only [hV]
  -- By the Cauchy-Schwarz inequality, $|V_n \cdot V_{n-1}| \leq \|V_n\| \|V_{n-1}\|$.
  -- So, $S_n = |-V_n \cdot V_{n-1}| = |V_n \cdot V_{n-1}| \leq \|V_n\| \|V_{n-1}\| = \sqrt{S_n} \sqrt{S_{n-1}}$.\
  have hCauchy : ∀ n, 1 ≤ n → S n ^ 2 ≤ S n * S (n - 1) := by
    intro n hn
    specialize hS1 n hn
    have : S n * S (n - 1) - S n ^ 2 = (V n 1 * V (n - 1) 0 - V n 0 * V (n - 1) 1) ^ 2 := by
      nth_rw 2 [hS1]
      simp [S]
      ring_nf
    nlinarith only [this]
  -- If $S_n > 0$, we can divide by $\sqrt{S_n}$ to get $\sqrt{S_n} \leq \sqrt{S_{n-1}}$, which implies $S_n \leq S_{n-1}$.\
  -- If $S_n = 0$, then $0 \leq S_{n-1}$ is also true (as $S_{n-1}$ is a sum of squares).\
  -- So, $S_n \leq S_{n-1}$ for all $n \geq 2$.
  have hS2 : ∀ n ,1 ≤ n → S n ≤ S (n - 1):= by
    intro n hn
    specialize hCauchy n hn
    rw [pow_two] at hCauchy
    by_cases h : S n > 0
    · nlinarith only [h,hCauchy]
    have h1 := hS n
    have h2 := hS (n - 1)
    omega
  -- The sequence $(S_n)_{n \geq 2}$ (i.e., $S_2, S_3, S_4, \ldots$) is a non-increasing sequence of non-negative integers.
  -- Such a sequence must eventually become constant. Let $N_0 \geq 2$ be an integer such that $S_n = S$ for all $n \geq N_0$, where $S$ is some non-negative integer.
  have hS3 : ∀ i j, S (i + j) ≤ S i := by
    intro i j
    induction j with
    | zero => simp
    | succ j ih =>
      specialize hS2 (i + (j + 1)) (by linarith)
      have : i + (j + 1) - 1 = i + j := by
        rw [← add_assoc]
        simp
      rw [this] at hS2
      linarith only [ih,hS2]
  have hS3 : ∃ N ,∀ n ,N ≤ n → S n = S (n + 1) := by
    by_contra! hN
    have : ∀ k : ℕ , ∃ n , S n < S 0 - k := by
      intro k
      have h0 := hN 0
      rcases h0 with ⟨n,⟨hN1,hN2⟩⟩ 
      induction k with
      | zero => 
        simp
        have : S (n + 1) < S n := by
          specialize hS2 (n + 1) (by linarith)
          simp at hS2
          omega
        specialize hS3 0 n
        use (n + 1)
        simp at hS3
        linarith   
      | succ k ih =>
        rcases ih with ⟨m, hm⟩
        specialize hN m
        rcases hN with ⟨t,⟨ht1,ht2⟩⟩
        have : S (t + 1) < S t := by
          specialize hS2 (t + 1) (by linarith)
          simp at hS2
          omega
        specialize hS3 m (t-m)
        use (t + 1)
        rw [add_comm,Nat.sub_add_cancel ht1] at hS3
        rw [Nat.cast_add]
        simp
        nlinarith
    specialize this (S 0).natAbs
    rcases this with ⟨n,hn⟩
    specialize hS n
    have : S 0 ≤ ↑(S 0).natAbs := by
      exact Int.le_natAbs
    linarith
  rcases hS3 with ⟨N,hN⟩
  have hN' : ∀ n , S (N + n) = S N := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, ← add_assoc, hN (N+n) (by linarith)]
  -- We consider two cases for the value of $S$:
  by_cases hS4 : S N = 0
  -- If $S=0$, then $S_n=0$ for all $n \geq N_0$.\
  -- $S_n = x_n^2+y_n^2 = 0$ implies $x_n=0$ and $y_n=0$ because $x_n, y_n$ are integers.
  · have hx : ∀ n , x (N + n) = 0 := by
      intro n
      specialize hN' n
      rw [hS4] at hN'
      simp [S,V] at hN'
      rw [← pow_two,← pow_two] at hN'
      nlinarith
    -- So, for all $n \geq N_0$, $x_n = a_n-a_{n-1} = 0$.\
    -- This means $a_n = a_{n-1}$ for all $n \geq N_0$.\
    -- Therefore, $a_n = a_{N_0-1}$ for all $n \geq N_0-1$. The sequence $a_n$ becomes constant from term $a_{N_0-1}$ onwards.
    have ha : ∀ n , a (N + n) = a N := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        specialize hx n
        simp [x] at hx
        rw [← add_assoc] ;linarith
    -- We need to prove that there exists a positive integer $k$ such that $a_{k+M}=a_{k+M^M}$.
    -- Let $k = N_0-1$. Since $N_0 \geq 2$, $k \geq 1$, so $k$ is a positive integer.
    -- Then for any positive integer $M$:\
    -- $k+M = N_0-1+M$. Since $M \geq 1$, $N_0-1+M \geq N_0-1+1 = N_0$.
    -- So $a_{k+M} = a_{N_0-1+M} = a_{N_0-1}$ (because $N_0-1+M \geq N_0-1$ and the sequence is constant from $a_{N_0-1}$).
    -- Also, $M^M \geq 1^1 = 1$ for any positive integer $M$.\
    -- So $k+M^M = N_0-1+M^M \geq N_0-1+1 = N_0$.\
    -- Thus, $a_{k+M^M} = a_{N_0-1+M^M} = a_{N_0-1}$.\
    -- So $a_{k+M}=a_{N_0-1}=a_{k+M^M}$. This proves the statement for Case 1.
    use (N + 1)
    constructor
    · linarith
    have h1 := ha (1 + M)
    have h2 := ha (1 + M ^ M)
    rw [← add_assoc] at h1 h2
    rw [h1,h2]
  -- Case 2: $S > 0$.\
  -- For $n \geq N_0$, we have $S_n = S_{n+1} = S > 0$.\
  -- The relation $S_{n+1} = -V_{n+1} \cdot V_n$ means $S = -V_{n+1} \cdot V_n$.
  -- Also, $\|V_{n+1}\|^2 = S$ and $\|V_n\|^2 = S$. So $\|V_{n+1}\| = \sqrt{S}$ and $\|V_n\| = \sqrt{S}$.\
  -- The Cauchy-Schwarz inequality becomes $S = |-V_{n+1} \cdot V_n| \leq \|V_{n+1}\| \|V_n\| = \sqrt{S}\sqrt{S} = S$.\
  -- This means that equality must hold in the Cauchy-Schwarz inequality. Equality holds if and only if $V_{n+1}$ and $V_n$ are linearly dependent.\
  -- So, $V_{n+1} = cV_n$ for some rational scalar $c$ (since components are integers).
  have hV1 : ∀ n, N ≤ n → ∃ c : ℝ, ↑(V (n + 1) 1) = c * (↑(V n 1) : ℝ) ∧ ↑(V (n + 1) 0) = c * (↑(V n 0) : ℝ) := by
    intro n hn
    have h1 : S (n + 1) * S n - S (n + 1) ^ 2 = 0 := by
      have h2 := hN' (n - N)
      have h3 := hN' (n + 1 - N)
      rw [add_comm,Nat.sub_add_cancel (by linarith)] at h2 h3
      rw [h2,h3] ;ring_nf
    have h3 : S (n + 1) * S n - S (n + 1) ^ 2 = (V (n + 1) 1 * V n 0 - V (n + 1) 0 * V n 1) ^ 2 := by
      specialize hS1 (n + 1) (by linarith)
      nth_rewrite 2 [hS1]
      simp [S] ;ring_nf
    rw [h3] at h1
    simp at h1
    by_cases hc : V n 1 ≠ 0 ∧ V n 0 ≠ 0
    use (↑(V (n + 1) 1) / ↑(V n 1))
    have : (↑(V (n + 1) 1) : ℝ) / ↑(V n 1) = ↑(V (n + 1) 0) / ↑(V n 0) := by
      apply (div_eq_div_iff (by simp ;omega) (by simp ;omega)).mpr
      rify at h1
      linarith
    nth_rewrite 2 [this]
    rw [div_mul_cancel₀,div_mul_cancel₀]
    simp
    simp ;omega
    simp ;omega
    simp at hc
    by_cases hc1 : V n 1 = 0
    · by_cases hc2 : V n 0 = 0
      · have : S n = 0 := by
          simp [S,hc1,hc2]
        specialize hN' (n - N)
        rw [add_comm,Nat.sub_add_cancel hn] at hN'
        rw [hN'] at this
        exact False.elim (hS4 this)
      use (↑(V (n + 1) 0) / ↑(V n 0))
      simp [hc1,hc2] at h1
      simp [hc1,h1,hc2]
    simp [hc1] at hc
    simp [hc,hc1] at h1
    simp [hc,h1]
    use (↑(V (n + 1) 1) / ↑(V n 1))
    simp [hc1]
  -- Since $S > 0$, we can divide by $S$ to get $1=-c$, so $c=-1$.
  -- Thus, $V_{n+1} = -V_n$ for all $n \geq N_0$.\
  -- This implies $x_{n+1} = -x_n$ and $y_{n+1} = -y_n$ for all $n \geq N_0$.
  have hx1 : ∀ n, N ≤ n → x (n + 1) = -x n ∧ y (n + 1) = -y n := by
    intro n hn
    specialize hV1 n hn
    specialize hS1 (n + 1) (by linarith)
    rcases hV1 with ⟨c,hc1,hc2⟩
    simp [S,V] at hc1 hc2 hS1
    rify at hS1
    nth_rewrite 3 [hc1,hc2] at hS1 
    have h1 := hN' (n + 1 -N)
    have h2 := hN' (n - N)
    rw [add_comm, Nat.sub_add_cancel (by linarith)] at h1 h2
    rw [← h2] at h1
    simp [S,V] at h1
    rify at h1
    rw [h1,← neg_mul,← neg_mul,← neg_mul,← neg_mul
    ,mul_assoc,mul_assoc,← mul_add] at hS1
    replace hS1 : (1 + c) * (↑(x n) * ↑(x n) + ↑(y n) * ↑(y n)) = 0 := by
      nth_rewrite 1 [add_mul,hS1]
      simp
    rw [← h2] at hS4
    simp [S,V] at hS4
    rify at hS4
    simp [hS4] at hS1
    rify
    have : c = -1 := by nlinarith only [hS1]
    rw [hc1,hc2,this] ;simp
  -- Now consider the sequence $a_n$. For $n \geq N_0$, $a_{n+1}-a_n = x_{n+1} = -x_n = -(a_n-a_{n-1})$.\
  -- Let $X = x_{N_0} = a_{N_0}-a_{N_0-1}$.
  let X := a (N + 1) - a N
  -- Then $x_{N_0+1} = -X$, $x_{N_0+2} = X$, and so on. In general, $x_{N_0+j} = (-1)^j X$ for $j \geq 0$.\
  -- Let's look at the terms of sequence $a_n$ for $n \geq N_0-1$:\
  -- $a_{N_0-1}$\
  -- $a_{N_0} = a_{N_0-1} + x_{N_0} = a_{N_0-1} + X$.\
  -- $a_{N_0+1} = a_{N_0} + x_{N_0+1} = (a_{N_0-1}+X) - X = a_{N_0-1}$.\
  -- $a_{N_0+2} = a_{N_0+1} + x_{N_0+2} = a_{N_0-1} + X$.\
  -- $a_{N_0+3} = a_{N_0+2} + x_{N_0+3} = (a_{N_0-1}+X) - X = a_{N_0-1}$.\
  -- So, for $j \geq 0$:\
  -- $a_{N_0-1+j} = a_{N_0-1}$ if $j$ is even.\
  -- $a_{N_0-1+j} = a_{N_0-1}+X (=a_{N_0})$ if $j$ is odd.
  have ha : ∀ n , a (N + 2 * n) = a N ∧ a (N + 2 * n + 1) = a N + X := by
    intro n
    induction n with
    | zero =>
      simp [X]
    | succ n ih =>
      have h1 : a (N + 2 * (n + 1)) - a (N + 2 * n + 1) = - (a (N + 2 * n + 1) - a (N + 2 * n)) := by
        specialize hx1 (N + 2 * n) (by linarith)
        rcases hx1 with ⟨hx1,_⟩
        simp [x] at hx1
        simp [← hx1] ;ring_nf
      have h2 : a (N + 2 * (n + 1) + 1) - a (N + 2 * (n + 1)) = - (a (N + 2 * (n + 1)) - a (N + 2 * n + 1)) := by
        specialize hx1 (N + 2 * n + 1) (by linarith)
        rcases hx1 with ⟨hx1,_⟩
        simp [x] at hx1
        simp [← hx1] ;ring_nf
      simp at h1 h2
      rw [h1,h2,ih.1,ih.2]
      simp
  -- If $X=0$, then $a_{N_0}-a_{N_0-1}=0$, so $a_{N_0}=a_{N_0-1}$. In this case $a_{N_0-1+j} = a_{N_0-1}$ for all $j \geq 0$. This means $a_n$ is constant for $n \geq N_0-1$, which is covered by Case 1. So we can assume $X \neq 0$.
  by_cases hX : X = 0
  · rw [hX,add_zero] at ha
    replace ha : ∀ n, a (N + n) = a N := by
      intro n
      have : Even n ∨ Odd n := Nat.even_or_odd n
      rcases this with ⟨d,hd⟩ | ⟨d,hd⟩
      specialize ha d
      rw [hd, ← two_mul,ha.1]
      specialize ha d
      rw [hd,← add_assoc,ha.2]
    use (N + 1)
    constructor
    · linarith
    rw [add_assoc,add_assoc,ha,ha]
  -- Let $k=N_0-1$. Since $N_0 \geq 2$, $k \geq 1$, so $k$ is a positive integer.\
  -- We want to compare $a_{k+M}$ and $a_{k+M^M}$.\
  -- $a_{k+M} = a_{N_0-1+M}$. This term is $a_{N_0-1}$ if $M$ is even, and $a_{N_0}$ if $M$ is odd.\
  -- $a_{k+M^M} = a_{N_0-1+M^M}$. This term is $a_{N_0-1}$ if $M^M$ is even, and $a_{N_0}$ if $M^M$ is odd.
  use (N+1)
  constructor
  · linarith
  have hM : Even M ∨ Odd M := Nat.even_or_odd M
  rcases hM with ⟨d,hd⟩ | ⟨d,hd⟩
  · have h1 := ha d
    nth_rewrite 1 [hd,← two_mul,add_assoc,add_comm 1,← add_assoc,h1.2]
    have : Even (M ^ M) := by
      apply Nat.even_pow.mpr
      nth_rewrite 1 [hd]
      simp ;linarith
    rcases this with ⟨e,he⟩
    specialize ha e
    rw [he,← two_mul,add_assoc,add_comm 1,← add_assoc,ha.2]
  have h1 := ha (d + 1)
  have : Odd (M ^ M) := by
    apply Odd.pow
    simp [hd]
  rcases this with ⟨e,he⟩
  specialize ha (e + 1)
  rw [he,hd]
  ring_nf at h1 ha
  ring_nf
  rw [h1.1,ha.1]
  

    

    
     

    
    

      
    
    
    
    