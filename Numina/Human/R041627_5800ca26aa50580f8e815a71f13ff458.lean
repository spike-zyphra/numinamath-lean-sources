import Mathlib

/- 1. Let $a$ and $b$ be real numbers such that $a+b=2$. Prove that

$$
\min \{|a|,|b|\}<1<\max \{|a|,|b|\} \Leftrightarrow a b \in(-3,1)
$$ -/

theorem algebra_220264 (a b : ℝ) (h : a + b = 2) :
    (min (abs a) (abs b) < 1 ∧ 1 < max (abs a) (abs b)) ↔ a * b ∈ Set.Ioo (-3) 1 := by 

    --Wlog we can assume that a ≤ b by symmetry.
    wlog aleb : a≤b
    have blea : b≤a := by linarith
    have tmp :   |b| ⊓ |a| < 1 ∧ 1 < |b| ⊔ |a| ↔ b * a ∈ Set.Ioo (-3) 1 := by 
      apply this b a;
      linarith
      exact blea
    constructor
    intro bound
    obtain ⟨lb,hb⟩ := bound
    have : |b|⊓|a| = |a| ⊓ |b| := by exact min_comm |b| |a|
    rw [this] at tmp
    have : |b|⊔|a| = |a| ⊔ |b| := by exact max_comm |b| |a|
    rw [this] at tmp
    rw [mul_comm]
    rw [←tmp]; tauto
    
    intro bound
    rw [mul_comm] at bound
    rw [← tmp] at bound
    have : |b|⊓|a| = |a| ⊓ |b| := by exact min_comm |b| |a|
    rw [this] at bound
    have : |b|⊔|a| = |a| ⊔ |b| := by exact max_comm |b| |a|
    rw [this] at bound
    assumption

    -- Then by a≤b, we get a ≤ 1 and 1 ≤ b.
    have : a ≤ 1 := by linarith
    have : 1 ≤ b := by linarith

    -- The remaining part is just simple calculation based on the definition.
    constructor
    intro h
    obtain ⟨lb, hb ⟩ := h
    simp

    have bne1 : b ≠ 1 := by 
      by_contra beq1
      have aeq1: a = 1 := by linarith
      rw [aeq1,beq1] at lb; norm_cast at lb
    have bg1: 1 < b := by 
      by_contra
      have : b ≤ 1 := by linarith
      have : b = 1 := by linarith
      contradiction
    have absbg1 : 1 < |b| := by 
      rw [lt_abs]; left; assumption
    have al1 : a < 1 := by linarith
    have agm3 : -3 < a := by
      by_contra
      have alem3 : a ≤ -3 := by linarith
      have : 1 ≤ |a| := by 
        rw [le_abs]; right; linarith
      have : 1 ≤ |a| ⊓ |b| := by simp; constructor; linarith; linarith
      linarith
    have bl3 : b < 3 := by 
      by_contra
      have bge3 : b ≥ 3 := by linarith
      have : a ≤ -1 := by linarith
      have : 1 ≤ |a| := by rw [le_abs]; right; linarith
      have : 1 ≤ |b| := by rw [le_abs]; left; linarith
      have : 1 ≤ |a| ⊓ |b| := by simp; constructor; linarith; linarith
      linarith

    constructor
    nlinarith
    nlinarith

    intro h
    simp at h
    obtain ⟨lb,hb⟩ := h

    have bne1 : b ≠ 1 := by nlinarith
    have ane1 : a ≠ 1 := by nlinarith
    have al1 : a < 1 := by nlinarith
    have bg1 : 1 < b := by nlinarith

    have : -1 < a := by nlinarith
    have : |a| < 1 := by rw [abs_lt]; constructor; linarith; linarith
    have : |a| ⊓ |b| ≤ |a| := by exact min_le_left |a| |b|
    constructor
    linarith

    have : b ≤ |b| := by exact le_abs_self b
    have : 1 < |b| := by linarith
    have : |b| ≤ |a| ⊔ |b| := by exact le_max_right |a| |b|
    linarith
      
