import Mathlib

-- https://app.projectnumina.ai/problems/0f4e4114-1ba0-5cf7-be19-8c7d4cc42d7a
/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ satisfying the equation  $$ f(x+f(x+y))+f(x y)=x+f(x+y)+y f(x) $$  for all real numbers $x$ and $y$. (Albania) Answer. There are two such functions, namely the identity function and $x \mapsto 2-x$. -/
theorem imo_24677:
    {f : ℝ → ℝ | ∀ x y, f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x} = {id, fun x => 2 - x} := by
    -- Prove set equality by proving mutual subset
    rw [subset_antisymm_iff, Set.subset_def, Set.subset_def]
    simp
    constructor
    . intro f h
      -- setting $y=1$ in `h`, we obtain $$ f(x+f(x+1))=x+f(x+1) $$
      -- in other words, $x+f(x+1)$ is a fixed point of $f$ for every $x \in \mathbb{R}$
      have h1: ∀ x: ℝ, f (x + f (x + 1)) = x + f (x + 1) := by
        intro x
        have h1' := h x 1
        rw [<-sub_eq_zero]
        rw [<-sub_eq_zero] at h1'
        ring_nf at h1'
        ring_nf
        exact h1'
      -- Distinguish two cases regarding the value of $f(0)$
      match Decidable.eq_or_ne (f 0) 0 with
      | Or.inl f0_eq_0 => {
        -- By letting $y=0$ and replacing $x$ by $x+1$ in `h`, we obtain $$ f(x+f(x+1)+1)=x+f(x+1)+1 $$
        have h2: ∀ x: ℝ, f (x + f (x + 1) + 1) = x + f (x + 1) + 1 := by
          intro x'
          have h' := h (x' + 1) 0
          rw [<-sub_eq_zero] at h'
          rw [<-sub_eq_zero, <-h']
          simp [f0_eq_0]
          ring_nf
        -- By letting $x=1$ in `h`, we obtain $$ f(1+f(y+1))+f(y)=1+f(y+1)+y f(1) $$
        have h3: ∀ y: ℝ, f (1 + f (1 + y)) + f y = 1 + f (1 + y) + y * f 1 := by
          intro y'
          have h' := h 1 y'
          rw [one_mul] at h'
          exact h'
        -- By letting $x=-1$ and $y=1$ in `h`, we obtain $f(-1)=-1$
        have f_neg_1: f (-1) = -1 := by
          have h' := h (-1) 1
          simp [f0_eq_0] at h'
          exact h'
        -- By letting $x=1$ and $y=-1$ in `h`, we obtain $f(1)=1$
        have f_1: f 1 = 1 := by
          have h' := h 1 (-1)
          rw [<-sub_eq_zero] at h'
          simp [f0_eq_0, f_neg_1] at h'
          ring_nf at h'
          calc f 1 = ((-2 + f 1 * 2) + 2) / 2 := by ring_nf
            _ = (0 + 2) / 2 := by rw [h']
            _ = 1 := by simp

        -- use $f(-1)=-1$ to simplify h3
        rw [f_1] at h3
        simp only [mul_one] at h3

        -- Accordingly, if both $y\_{0}$ and $y\_{0}+1$ are fixed points of $f$, then so is $y\_{0}+2$.
        have h4 {y: ℝ} (fp1: f y = y) (fp2: f (y + 1) = y + 1) : f (y + 2) = y + 2 := by
          have h' := h3 y
          simp only [add_comm, fp2, fp1, add_right_inj] at h'
          ring_nf at h'
          rw [add_comm] at h'
          exact h'
        -- Thus, it follows from `h1` and `h2` that $x+f(x+1)+2$ is a fixed point of $f$ for every $x \in \mathbb{R}$;
        have h5: ∀ x: ℝ, f (x + f (x + 1) + 2) = x + f (x + 1) + 2 := fun x => h4 (h1 x) (h2 x)

        -- Replacing $x$ by $x-2$ simplifies the above equation to $$ f(x+f(x-1))=x+f(x-1) $$
        -- On the other hand, we set $y=-1$ in `h` and get $$ f(x+f(x-1))=x+f(x-1)-f(x)-f(-x) $$
        -- Therefore, $f(-x)=-f(x)$ for all $x \in \mathbb{R}$.
        have f_odd: ∀ x : ℝ, f (-x) = - f x := by
          intro x
          have h' := h5 (x - 2)
          ring_nf at h'
          have h'' := h x (-1)
          ring_nf at h''
          rw [h'] at h''
          rw [<-sub_eq_zero] at h''
          rw [<-sub_eq_zero]
          ring_nf at h''
          ring_nf
          exact h''

        left
        funext y

        -- substitute $(x, y)$ by $(-1,-y)$ in `h`
        have h6 := h (-1) (-y)
        -- simplify `h6` by the fact that $f$ is an odd function
        have m {a b : ℝ}: f (-a + -b) = f (- (a + b)) := by ring_nf
        simp only [mul_neg, neg_mul, one_mul, neg_neg, f_neg_1, m, f_odd] at h6
        -- transfrom `h3`
        have h7: f (1 + f (1 + y)) = 1 + f (1 + y) + y - f y := by
          have h' := h3 y
          rw [<-sub_eq_zero] at h'
          rw [<-sub_eq_zero, <-h']
          ring_nf
        -- substitute `h7` into `h6`, we obtain $f(x) = x$
        rw [h7] at h6
        rw [<-sub_eq_zero] at h6
        ring_nf at h6
        rw [<-mul_left_inj' (show (2:ℝ) ≠ 0 by norm_num)]
        rw [<-sub_eq_zero, <-h6, id_eq]
        ring_nf
      }
      | Or.inr f0_ne_0 => {
        -- By letting $x=0$ and $y=x' + f (x' + 1)$ in h, we have $$ f(f(y))+f(0)=f(y)+y f(0) $$
        -- and $y$ is a fixed point of $f$. So, $x+f(x+1)=1$ for all $x \in \mathbb{R}$
        have h2: ∀ x: ℝ, x + f (x + 1) = 1 := by
          intro x'
          have h' := h 0 (x' + f (x' + 1))
          simp [(h1 x'), f0_ne_0] at h'
          exact h'
        right
        funext x'
        -- By letting $x = x - 1$ in `h2`, we have $f(x)=2-x$ for all $x \in \mathbb{R}$.
        replace h2 := h2 (x' - 1)
        rw [<-sub_eq_zero] at h2
        rw [<-sub_eq_zero, <- h2]
        ring_nf
      }
    -- prove both functions satisfy the equation
    . ring_nf
      simp
      intros x y
      ring_nf
