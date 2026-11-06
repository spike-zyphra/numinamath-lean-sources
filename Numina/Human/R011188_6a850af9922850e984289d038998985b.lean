import Mathlib

/- 2. (BUL 3) Let $a_{0}, a_{1}, \ldots, a_{n}, a_{n+1}$ be a sequence of real numbers satisfying the following conditions:  $$ \begin{aligned} a_{0} & =a_{n+1}=0 \\ \left|a_{k-1}-2 a_{k}+a_{k+1}\right| & \leq 1 \quad(k=1,2, \ldots, n) \end{aligned} $$  Prove that $\left|a_{k}\right| \leq \frac{k(n+1-k)}{2}(k=0,1, \ldots, n+1)$. -/


lemma seq {n : ℕ} (c : ℕ → ℝ) (h0: c 0 = 0) (hnp1: c (n+1) = 0) (h : ∀ k ∈ Finset.Icc 1 n, 2* c k ≤ c (k-1) + c (k+1)) : ∀ k ∈ Finset.Icc 0 (n+1), c k ≤ 0:= by 
  --A lemma about sequences satisfing 2c_k <= c_(k-1) + c_(k+1): the maximum of these seqences is ahiceved at endpoints.

  --The case n = 0 is trivial.
  by_cases ne0 : n = 0
  simp [ne0] at hnp1 ⊢
  intro k kle1
  by_cases ke0 : k = 0
  simp [ke0, h0]
  have ke1 : k = 1 := by omega
  simp [ke1,hnp1]
  have npos : 0 < n := by positivity
  
  --For other cases, we prove it by a double induction.
  intro k
  induction' k with k hk
  
  simp [h0]
  intro ub
  simp at ub
  simp at hk
  have cknpos : c k ≤ 0 := by apply hk; linarith

  by_contra ckp1pos
  push_neg at ckp1pos

  have knen : k ≠ n := by 
    by_contra ken
    rw [ken] at ckp1pos
    simp [hnp1] at ckp1pos
  have exi : ∃ i:ℕ, k+i = n := by use (n-k); omega
  
  have cla : ∀ i:ℕ, k+i ≤ n → c (k+i) < c (k+i+1) ∧ 0 < c (k+i+1) := by 
    intro i
    induction' i with i hi
    
    simp [ub]
    constructor;
    linarith
    exact ckp1pos

    intro uu
    have : k + i ≤ n := by linarith
    apply hi at this
    obtain ⟨ckpi, cipop1pos⟩ := this

    have t: c (k + (i + 1)) < c (k + (i + 1) + 1) := by 
      specialize h (k+(i+1))
      simp [uu] at h
      have : 1 ≤ k + (i + 1) := by omega
      simp [this] at h
      rw [add_assoc] at ckpi
      linarith

    constructor
    exact t
    nth_rw 1 [←add_assoc] at t
    linarith

  obtain ⟨i,hi⟩ := exi
  specialize cla i
  simp [hi] at cla
  simp [hnp1] at cla


theorem inequalities_25087 {n : ℕ} (a : ℕ → ℝ) (h₀ : a 0 = 0) (h₁ : a (n + 1) = 0) (h₂ : ∀ k ∈ Finset.Icc 1 n, |a (k - 1) - 2 * a k + a (k + 1)| ≤ 1) :
  ∀ k ∈ Finset.Icc 0 (n + 1), |a k| ≤ (k * (n + 1 - k)) / 2 := by 
  
  intro k hk
  --By symmetry, we only need to consider the cases that 0 ≤ a k.
  wlog akge0 : 0 ≤ a k
  let b : ℕ → ℝ := fun n => - (a n)
  have : |b k| ≤ ↑k * (↑n + 1 - ↑k) / 2 := by 
    apply this
    simp [b, h₀]
    simp [b, h₁]
    intro k hk
    have t: |a (k - 1) - 2 * a k + a (k + 1)| ≤ 1 := h₂ k hk
    have : |b (k - 1) - 2 * b k + b (k + 1)| = |a (k - 1) - 2 * a k + a (k + 1)| := by 
      simp [b]
      have : -a (k - 1) + 2 * a k + -a (k + 1) = - (a (k-1) - 2 * a k + a (k+1)) := by ring
      rw [this]
      exact abs_neg (a (k - 1) - 2 * a k + a (k + 1))
    rw [this]; exact t
    exact hk
    simp [b]; linarith 
  simp [b] at this
  exact this

  have : |a k| = a k := by exact abs_of_nonneg akge0
  rw [this]

  --Now, let b_i = i(n+1-i)/2 and c = a i - b i. We prove that c satisfies the assumption of the lemma.
  let b : ℕ → ℝ := fun i => i*(n+1-i)/2
  let c : ℕ → ℝ := fun i => a i - b i

  have t1 : ∀ k ∈ Finset.Icc 1 n, b (k-1) - 2*b k + b (k+1) = -1 := by 
    intro k hk
    simp at hk
    obtain ⟨kl,ku⟩ := hk
    simp [b]
    field_simp
    ring
  have t2 : ∀ k ∈ Finset.Icc 1 n, -1 ≤ a (k-1) - 2 * a k + a (k+1) := by 
    intro k hk
    specialize h₂ k hk
    exact neg_le_of_abs_le h₂
  have t3 : ∀ k ∈ Finset.Icc 1 n, 2 * c k ≤ c (k-1) + c (k+1) := by 
    intro k hk
    specialize t1 k hk
    specialize t2 k hk
    simp [c]
    linarith
  --By the lemma, we get that c i ≤ 0, so a i ≤ b i for every i, which is what we need.
  have cla : ∀ k ∈ Finset.Icc 0 (n+1), c k ≤ 0 := by 
    apply seq
    simp [c]
    simp [b] 
    exact h₀
    simp [c]
    simp [b]
    exact h₁
    exact t3

  specialize cla k hk
  simp [c,b] at cla
  exact cla
