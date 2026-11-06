import Mathlib

open Real Set
open scoped BigOperators

/- 1. (YUG) Find all real numbers $x \in[0,2 \pi]$ such that  $$ 2 \cos x \leq|\sqrt{1+\sin 2 x}-\sqrt{1-\sin 2 x}| \leq \sqrt{2} $$ -/
theorem inequalities_24572 {x : ℝ} (hx : x ∈ Icc 0 (2 * π)) :
    2 * cos x ≤ abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ∧
    abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ↔ π / 4 ≤ x ∧ x ≤ 7 * π / 4 := by 
  --We first show that the second inequality is always true.
  have eq : (√(1 + sin (2 * x)) - √(1 - sin (2 * x)))^2 = 2 - 2 * |cos (2*x)| := by 
    have l1 : (√(1 + sin (2 * x)) - √(1 - sin (2 * x)))^2 = 2 - 2 * √(1- sin (2*x) ^2) := by 
      have t1 : 0 ≤ 1 + sin (x*2) := by 
        have : -1 ≤ sin (x*2) := by exact neg_one_le_sin (x * 2)
        linarith only [this]
      have t2 : 0 ≤ 1 - sin (x*2) := by 
        have : sin (x*2) ≤ 1 := by exact sin_le_one (x * 2)
        linarith only [this]
      ring_nf
      have t3 : √(1 + sin (x * 2)) ^ 2 = 1 + sin (x*2) := by exact sq_sqrt t1
      have t4 : √(1 - sin (x * 2)) ^ 2 = 1 - sin (x*2) := by exact sq_sqrt t2
      rw [t3,t4]
      have t5 : √(1 + sin (x * 2)) * √(1 - sin (x * 2)) = √((1 + sin (x * 2)) * (1 - sin (x * 2))) := by exact Eq.symm (sqrt_mul' (1 + sin (x * 2)) t2)
      rw [t5]
      ring_nf
    rw [l1]
    have l2 : √(1 - sin (2 * x) ^ 2) = |cos (2*x)| := by 
      rw [← Real.cos_sq']
      exact sqrt_sq_eq_abs (cos (2 * x))
    rw [l2]
  have ri: abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ↔ True := by 
    have tmp1 : abs (sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))) ≤ sqrt 2 ↔ (√(1 + sin (2 * x)) - √(1 - sin (2 * x)))^2 ≤ (sqrt 2)^2 := by 
      rw [sq_le_sq];
      have : |sqrt 2| = sqrt 2 := by 
        have : 0 ≤ sqrt 2 := by exact sqrt_nonneg 2
        exact abs_of_nonneg this
      rw [this]
    have tmp2 : @HPow.hPow ℝ ℕ ℝ instHPow (√2) 2 = 2 := by refine sq_sqrt ?_; norm_num
    simp [tmp1,eq,tmp2]
  simp [ri]

  --Hence, we only need to consider the first one.
  --We will prove that the first inequality is true iff cos (2*x) ≤ 0 ∨ cos x < 0.
  simp at hx
  --Then, we use the following fact about cos x ≤ 0 and cos (2*x) ≤ 0 to finish the proof.
  have cosnposiff : cos x ≤ 0 ↔ π /2 ≤ x ∧ x ≤ 3*π/2:= by 
    constructor
    intro h
    by_contra hn
    push_neg at hn
    by_cases xlpio2 : x < π/2
    have : 0 < cos x := by 
      apply cos_pos_of_mem_Ioo;
      simp [hx,xlpio2]
      linarith
    linarith only [h,this]
    have lb: π /2 ≤ x := by linarith 
    apply hn at lb
    have : 0 < cos x := by
      have : cos x = cos (x - 2*π) := by simp
      rw [this]
      apply cos_pos_of_mem_Ioo
      simp
      constructor
      have : 2 * π = π /2 +  3 * π / 2 := by ring
      rw [this]
      linarith only [lb]
      have t1 : 2*π - 2*π = 0 := by ring
      have t2 : 0 < π / 2 := by positivity
      linarith
    linarith only [this, h]

    intro h
    obtain ⟨lb,ub⟩ := h
    apply Real.cos_nonpos_of_pi_div_two_le_of_le
    exact lb
    linarith

  have cos2nposiff : cos (2*x) ≤ 0 ↔ π /4 ≤ x ∧ x ≤ 3*π /4 ∨ 5*π /4 ≤ x ∧ x ≤ 7*π /4 := by 
    constructor

    intro h
    by_cases xl1 : x < π /4
    have t1: 2*x < π /2 := by linarith
    have t2: 0 ≤ 2 * x := by linarith
    have : 0 < cos (2*x) := by 
      apply Real.cos_pos_of_mem_Ioo; 
      simp [t1,t2]
      linarith
    linarith only [h,this]
    by_cases x2 : π / 4 ≤ x ∧ x ≤ 3 * π / 4 
    left
    exact x2
    by_cases x3 : 3 * π / 4 < x ∧ x < 5 * π / 4
    obtain ⟨ll,uu⟩ := x3
    have t1: -(π /2) < 2*x -2*π := by linarith
    have t2: 2*x -2*π ≤ (π /2)  := by linarith
    have tmp : cos (2*x) = cos (2*x - 2*π) := by simp
    have : 0 < cos (2*x) := by 
      rw [tmp]
      apply Real.cos_pos_of_mem_Ioo
      simp
      constructor
      linarith
      linarith
    linarith only [h,this]
    by_cases x4 : 5 * π / 4 ≤ x ∧ x ≤ 7 * π / 4
    right
    exact x4
    have x5: 7*π /4 < x := by 
      push_neg at xl1 x2 x3 x4
      apply x4
      apply x3
      apply x2
      exact xl1
    have t1: -(π /2) < 2*x -4*π := by linarith
    have t2: 2*x -4*π ≤ π / 2  := by linarith
    have tmp : cos (2*x) = cos (2*x - 4*π) := by 
      have : cos (2*x) = cos (2*x - 2 * π) := by simp
      have : cos (2*x - 2*π ) = cos (2*x - 4*π) := by 
        have : 2*x - 4*π = 2*x - 2*π - 2*π := by ring
        rw [this]
        simp
      linarith
    have : 0 < cos (2*x) := by 
      rw [tmp]
      apply Real.cos_pos_of_mem_Ioo
      simp
      constructor
      linarith
      linarith
    linarith only [h,this]

    intro h
    rcases h with h | h
    
    obtain ⟨lb, ub⟩ := h
    have t1: π / 2 ≤ 2 * x := by linarith
    have t2: 2 * x ≤ π + π / 2 := by linarith
    apply cos_nonpos_of_pi_div_two_le_of_le
    exact t1
    linarith

    obtain ⟨lb,ub⟩ :=h
    have t1: 5*π/2 ≤ 2*x := by linarith
    have t2: 2*x ≤ 7*x/2 := by linarith
    have t3: π/2 ≤ 2*x - 2*π := by linarith
    have t4: 2*x - 2*π ≤ 3*x/2 := by linarith
    have : cos (2*x) = cos (2*x - 2 * π ) := by simp
    rw [this]
    apply cos_nonpos_of_pi_div_two_le_of_le
    linarith
    linarith


  --If cos x < 0, then the first inequality is trivially true.
  --When 0 ≤ cos x, we show that we need cos (2*x) ≤ 0 by rewriting our assumptions.
  have cla : (0 < cos x) → (2 * cos x ≤ |√(1 + sin (2 * x)) - √(1 - sin (2 * x))| ↔ (cos (2*x) ≤ 0)) := by 
    intro cospos
    have t1 : 2 * cos x ≤ |√(1 + sin (2 * x)) - √(1 - sin (2 * x))| ↔ 2 + 2 * cos (2*x) ≤ 2 - 2 * |cos (2*x)| := by 
      have l1 : 2 * cos x ≤ |√(1 + sin (2 * x)) - √(1 - sin (2 * x))| ↔ (2 * cos x)^2 ≤ (√(1 + sin (2 * x)) - √(1 - sin (2 * x)))^2 := by 
        rw [sq_le_sq]
        have : 2 * cos x = |2 * cos x| := by 
          symm
          apply abs_of_pos
          linarith only [cospos]
        nth_rw 1 [this]
      rw [l1]
      have eq1 : (2 * cos x)^2 = 2 + 2 * cos (2*x) := by rw [cos_two_mul]; ring
      rw [eq1,eq]
    rw [t1]
    
    constructor
    intro h
    have l1: cos (2*x) ≤ -|cos (2*x)| := by linarith
    have l2: 0 ≤ |cos (2*x)| := by exact abs_nonneg (cos (2 * x))
    linarith only [l1,l2]
    intro h
    have : |cos (2*x)| = (-cos (2*x)) := by exact abs_of_nonpos h
    rw [this]
    ring_nf
    exact Preorder.le_refl (2 + cos (x * 2) * 2)
    

  have cla2 : (2 * cos x ≤ |√(1 + sin (2 * x)) - √(1 - sin (2 * x))|  ↔ (cos x ≤ 0 ∨ (cos (2*x) ≤ 0))) := by 
    constructor

    intro h
    by_cases cosnpos : cos x ≤ 0
    left
    linarith only [cosnpos]
    have conspos : 0 < cos x := by linarith only [cosnpos]
    apply cla at conspos
    rw [conspos] at h
    right
    exact h

    intro h
    by_cases consnpos : cos x ≤ 0
    have : 0 ≤ |√(1 + sin (2 * x)) - √(1 - sin (2 * x))| := by exact abs_nonneg (√(1 + sin (2 * x)) - √(1 - sin (2 * x)))
    linarith only [consnpos,this]
    simp [consnpos] at h
    have conspos : 0 < cos x := by linarith only [consnpos]
    apply cla at conspos
    rw [conspos]
    exact h
    
  
  --The remaining part of the proof is trivial, just to put all conditions together.
  rw [cosnposiff,cos2nposiff] at cla2
  rw [cla2]
  
  constructor
  intro h
  rcases h with h | h | h <;>
  exact ⟨by linarith, by linarith⟩
  intro h
  by_cases l1 :x ≤ π /2 
  right; left
  exact ⟨by linarith, by linarith⟩
  push_neg at l1
  by_cases l2 : x ≤ 3*π /2
  left
  exact ⟨by linarith, by linarith⟩
  have : 3*π /2 ≤ x := by linarith
  right; right;
  exact ⟨by linarith, by linarith⟩

  