import Mathlib

/-33. (MON 4) In what case does the system \[  $$ \begin{aligned} & x+y+m z=a, \\ & x+m y+z=b, \\ & m x+y+z=c, \end{aligned} $$ \]  have a solution? Find the conditions under which the unique solution of the above system is an arithmetic progression.-/
theorem other_24672_1 {m a b c: ℝ} : let A := !![1,1,m;1,m,1;m,1,1];
(∃! v, Matrix.mulVec A v = ![a, b, c]) ↔ m ≠ 1 ∧ m ≠ -2 := by
-- We prove that the system of equations has a unique solution if and only if $m$ is not $1$ or $-2$
  intro A; constructor
-- Suppose $m$ is $-2$ or $1$, we exhibit two different solutions to the system of equations
  · contrapose!; intro meq exuni; rcases exuni with ⟨v, ⟨hv1, hv2⟩⟩
    simp at hv1 hv2; by_cases h' : m ≠ 1
    · replace meq := meq h'
      simp [A, Matrix.vecHead, Matrix.vecTail, meq] at hv1
    -- When $m$ is $-2$, prove that $c$ must be equal to $-(a+b)$
      have abcadd : c = - (a + b) := by
        rw [← add_eq_zero_iff_eq_neg]
        have : v 0 + (v 1 + -(2 * v 2)) = a := by
          apply_fun fun t => Function.eval 0 t at hv1
          simp at hv1; assumption
        rw [← this]
        have : v 0 + (-(2 * v 1) + v 2) = b := by
          apply_fun fun t => Function.eval 1 t at hv1
          simp at hv1; assumption
        rw [← this]
        have : -(2 * v 0) + (v 1 + v 2) = c := by
          apply_fun fun t => Function.eval 2 t at hv1
          simp at hv1; assumption
        rw [← this]; ring
    -- When $m$ is $-2$, the following two vectors $y1$ and $y2$ are obviously different, we show that they both are solutions to the system of equations
      set y1 := ![2/3*a+b/3,a/3-b/3,0] with h1; set y2 := ![2/3*a+b/3+1,a/3-b/3+1,1] with h2
      have y1ney2 : y1 ≠ y2 := by
        intro h; apply_fun fun t => Function.eval 0 t at h
        simp [h1, h2] at h
      have Amul1eq : A.mulVec y1 = ![a, b, c] := by
        simp [A, meq, Matrix.vecHead, Matrix.vecTail]
        rw [h1, abcadd]; norm_num; ring_nf
      have Amul2eq : A.mulVec y2 = ![a, b, c] := by
        simp [A, meq, Matrix.vecHead, Matrix.vecTail]
        rw [h2, abcadd]; norm_num; ring_nf
      have := hv2 y1 Amul1eq; rw [this] at y1ney2
      have := hv2 y2 Amul2eq; rw [this] at y1ney2; contradiction
    push_neg at h'; simp [A, Matrix.vecHead, Matrix.vecTail, h'] at hv1
  -- When $m$ is $1$, prove that $a$, $b$ and $c$ are equal
    have bceqa : b = a ∧ c = a := by
      let aeq := hv1; let beq := hv1; let ceq := hv1
      apply_fun fun t => Function.eval 0 t at aeq
      apply_fun fun t => Function.eval 1 t at beq
      apply_fun fun t => Function.eval 2 t at ceq
      simp at aeq beq ceq; rw [← aeq, ← beq, ← ceq]; ring_nf
      simp
  -- When $m$ is $-2$, the following two vectors $y1$ and $y2$ are obviously different, we show that they both are solutions to the system of equations
    set y1 := ![0,0,a] with h1; set y2 := ![1,-1,a] with h2
    have yneq : y1 ≠ y2 := by
      intro h; rw [h1, h2] at h
      apply_fun fun t => Function.eval 0 t at h; simp at h
    have Amul1eq : A.mulVec y1 = ![a, b, c] := by
      simp [A, h', Matrix.vecHead, Matrix.vecTail]
      rw [h1, bceqa.left, bceqa.right]; norm_num
    have Amul2eq : A.mulVec y2 = ![a, b, c] := by
      simp [A, h', Matrix.vecHead, Matrix.vecTail]
      rw [h2, bceqa.left, bceqa.right]; norm_num
    have := hv2 y1 Amul1eq; rw [this] at yneq
    have := hv2 y2 Amul2eq; rw [this] at yneq; contradiction
-- Conversely, we assume that $m$ is not $1$ or $-2$. Apply exists_unique_of_exists_of_unique to rewrite the goal
  intro hm; apply exists_unique_of_exists_of_unique
-- For the existance part of the goal, we explicitly write out the solution and check it indeed solve the equations
  · set v := ![(b+a-(1+m)*c)/((2+m)*(1-m)),(a+c-(1+m)*b)/((2+m)*(1-m)),(b+c-(1+m)*a)/((2+m)*(1-m))] with hv
    use v; simp [A, Matrix.vecHead, Matrix.vecTail]
    rw [hv]; norm_num
  -- In order to properly use field_simp, we need the following nonzero result
    have : (2 + m) * (1 - m) ≠ 0 := by
      rcases hm; simp; push_neg; constructor
      · intro h; rw [add_eq_zero_iff_neg_eq] at h; symm at h; contradiction
      intro h; rw [sub_eq_zero] at h; symm at h; contradiction
    field_simp; rw [show b+a-(1+m)*c+(a+c-(1+m)*b+m*(b+c-(1+m)*a)) = a*((2+m)*(1-m)) by ring]
    rw [show b+a-(1+m)*c+(m*(a+c-(1+m)*b)+(b+c-(1+m)*a)) = b*((2+m)*(1-m)) by ring]
    rw [show m*(b+a-(1+m)*c)+(a+c-(1+m)*b+(b+c-(1+m)*a)) = c*((2+m)*(1-m)) by ring]
    field_simp
-- For the uniqueness part of the goal, we first prove $A$ is an invertible matrix
  have invA : Invertible A := by
    apply Matrix.invertibleOfIsUnitDet
    simp [A, Matrix.det_fin_three, Matrix.vecHead, Matrix.vecTail]
    ring_nf; rw [show -2 + (m * 3 - m ^ 3) = -(m-1)^2*(m+2) by ring]; simp
    constructor; rw [sub_eq_zero]; push_neg; exact hm.left
    rw [add_eq_zero_iff_eq_neg]; push_neg; exact hm.right
-- Apply Matrix.mulVec_injective_of_invertible to show that A.mulVec is an injective function, and this is enough to finish the final goal
  suffices : Function.Injective A.mulVec
  · intro y1 y2 h1 h2; rw [← h2] at h1
    apply this at h1; assumption
  apply Matrix.mulVec_injective_of_invertible

/-33. (MON 4) In what case does the system \[  $$ \begin{aligned} & x+y+m z=a, \\ & x+m y+z=b, \\ & m x+y+z=c, \end{aligned} $$ \]  have a solution? Find the conditions under which the unique solution of the above system is an arithmetic progression.-/
theorem other_24672_2 {m a b c: ℝ} (hm : m ≠ 1 ∧ m ≠ -2) : let A := !![1,1,m;1,m,1;m,1,1];
Matrix.mulVec A v = ![a, b, c] → (v 0 + v 2 = 2 * v 1 ↔ a + c = 2 * b) := by
-- We show that if the system of equations has one unique solution, then it forms an arithmetic progression if and only if $a$, $b$, $c$ forms one
  intro A vsl
-- Denote the explicit solution by $w$
  set w := ![(b+a-(1+m)*c)/((2+m)*(1-m)),(a+c-(1+m)*b)/((2+m)*(1-m)),(b+c-(1+m)*a)/((2+m)*(1-m))] with hw
-- In order to properly use field_simp, we need the following nonzero result
  have : (2 + m) * (1 - m) ≠ 0 := by
    rcases hm; simp; push_neg; constructor
    · intro h; rw [add_eq_zero_iff_neg_eq] at h; symm at h; contradiction
    intro h; rw [sub_eq_zero] at h; symm at h; contradiction
-- Check that $w$ solves the equation
  have wsl : A.mulVec w = ![a, b, c] := by
    simp [A, Matrix.vecHead, Matrix.vecTail]; rw [hw]; norm_num
    field_simp; rw [show b+a-(1+m)*c+(a+c-(1+m)*b+m*(b+c-(1+m)*a)) = a*((2+m)*(1-m)) by ring]
    rw [show b+a-(1+m)*c+(m*(a+c-(1+m)*b)+(b+c-(1+m)*a)) = b*((2+m)*(1-m)) by ring]
    rw [show m*(b+a-(1+m)*c)+(a+c-(1+m)*b+(b+c-(1+m)*a)) = c*((2+m)*(1-m)) by ring]
    field_simp
-- Assume the given solution $v$ is equal to $w$, prove the final goal by explicit computation
  suffices : v = w
  · rw [this, hw]; field_simp; ring_nf; constructor
    · intro h; symm at h; apply_fun fun t => t + b * 2 + b * m * 2 + m * a + m * c at h
      ring_nf at h; rw [show m*a+m*c+a*2+c*2 = (m+2)*(a+c) by ring] at h
      rw [show  b*4+b*m*2 = (m+2)*(b*2) by ring, mul_eq_mul_left_iff] at h
      rcases h with h|h; assumption; rw [add_eq_zero_iff_eq_neg] at h
      rw [h] at hm; simp at hm
    intro h; rw [show b*m*2 = b*2*m by ring, ← h]; ring
-- Apply the above proved theorem other_24672_1, prove that $v$ is equal to $w$
  obtain ⟨v', ⟨_, hv'2⟩⟩ := (@other_24672_1 m a b c).mpr hm
  simp [A, Matrix.vecHead, Matrix.vecTail] at hv'2 vsl wsl
  have veq := hv'2 v vsl; have weq := hv'2 w wsl
  rw [← weq] at veq; simp [w] at veq; assumption