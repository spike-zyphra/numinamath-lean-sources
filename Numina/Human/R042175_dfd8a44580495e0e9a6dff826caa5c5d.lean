import Mathlib

def A : Set (ℝ × ℝ) := {(x, y) | ∀ a : ℝ, (a*x-1≠ 0) → y ≠ (x - a) / (a * x - 1)}
def B : Set (ℝ × ℝ) := {(x, y) | ∃ a : ℝ, a * (1 + x * y) = x + y}

/- 1. Let $A$ and $B$ be subsets of $\mathbb{R}^{2}=\mathbb{R} \times \mathbb{R}$ defined by:

$$
\begin{aligned}
& A=\left\{(x, y) \mid \text { for every } a \in \mathbb{R}, y \neq \frac{x-a}{a x-1}\right\} \\
& B=\{(x, y) \mid \text { there exists } a \in \mathbb{R}, a(1+x y)=x+y\}
\end{aligned}
$$

Find $A \cap B$, and then represent it graphically. -/
theorem algebra_223144 : A ∩ B = {(x, y) | x ^ 2 = 1 ∧ x * y ≠ -1} := by
  ext ⟨x, y⟩
  constructor

  --From left to right.
  intro h
  simp [A,B] at h
  simp

  obtain ⟨h1,h2⟩ := h
  obtain ⟨a,ha⟩ := h2
  
  --We use h2 first.
  --We first have a*x = 1.
  have axm1 : a * x - 1 = 0 := by 
    by_contra neq0
    have l1: ¬y = (x - a) / (a * x - 1) := by apply h1; assumption
    have : y*(a*x-1) = x - a := by nlinarith
    rw [←this] at l1;
    field_simp at l1
  have axe1 : a*x = 1 := by linarith

  --Then we get x=a and x^1 = 1.
  have : a + a*x*y = x + y := by nlinarith
  rw [axe1] at this
  ring_nf at this
  have xea: x = a := by linarith
  rw[← xea] at axe1

  have cx : x = 1 ∨ x = -1 := by exact mul_self_eq_one_iff.mp axe1 
  have : ¬ x*y= -1 := by
    rcases cx with x1 | xm1
    
    simp [x1] at xea this axm1 h1 ⊢
    specialize h1 0;
    norm_num at h1
    assumption

    simp [xm1] at xea this axm1 h1 ⊢
    specialize h1 0;
    norm_num at h1
    assumption


  tauto
  


  --From right to left. It's a simple verification.
  intro h
  simp [A,B]
  simp at h
  obtain ⟨h1, h2⟩ := h

  rcases h1 with xe1 | xem1
  
  constructor
  intro a ha
  simp [xe1] at h2 ha ⊢
  have : (1-a)/(a-1) = - (a-1)/(a-1) := by ring
  rw [this]
  have : - (a-1)/(a-1) = -1 := by field_simp
  rw [this]; assumption

  simp [xe1] at h2 ⊢
  use 1; simp
  
  constructor
  intro a ha
  simp [xem1] at h2 ha ⊢
  push_neg at ha
  have : (-1-a)/(-a-1) = 1 := by field_simp [ha]; ring
  rw [this]; assumption

  simp [xem1] at h2 ⊢
  use -1; simp
  linarith