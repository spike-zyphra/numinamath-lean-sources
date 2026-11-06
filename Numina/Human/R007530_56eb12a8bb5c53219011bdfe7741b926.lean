import Mathlib

/- Let $\mathbb{R}$ denote the set of real numbers. Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that

$$
f(x f(y)+y)+f(-f(x))=f(y f(x)-y)+y \quad \text { for all } x, y \in \mathbb{R}
$$ -/
theorem algebra_604790 (f : ℝ → ℝ) :
    (∀ x y, f (x * f y + y) + f (-f x) = f (y * f x - y) + y) ↔
    ∀ x, f x = x + 1 := by
      constructor
      · intro h
        --Let $f(0)=c$.
        let c := f 0
        --We make the following substitutions in the initial equation:
        let P x y := (f (x * f y + y) + f (-f x) = f (y * f x - y) + y)
        --1. $x=0, y=0
        have h1 : f (-c) = 0 := by
          have h11 : P 0 0 := h 0 0
          unfold P at h11
          --\Longrightarrow f(0)+f(-c)=f(0)
          simp only [zero_mul, add_zero, sub_self, add_right_eq_self] at h11
          --\Longrightarrow f(-c)=0$.
          exact h11
        --2. $x=0, y=-c
        have h2 : f (c - c ^ 2) = c := by
          have h21 : P 0 (-c) := h 0 (-c)
          unfold P at h21
          --\Longrightarrow f(-c)+f(-c)=f\left(c-c^{2}\right)-c 
          simp only [h1, mul_zero, zero_add, add_zero, neg_mul, sub_neg_eq_add] at h21
          --\Longrightarrow f\left(c-c^{2}\right)=c$.
          calc
            _ = f (c - c ^ 2) - 0 := by simp only [sub_zero]
            _ = f (c - c ^ 2) - (f (-(c * f 0) + c) + -c) := by nth_rw 1 [h21]
            _ = _ := by ring_nf
        --3. $x=-c, y=-c
        have h3 : f (c) = 2 * c := by
          have h31 : P (-c) (-c) := h (-c) (-c)
          unfold P at h31
          --\Longrightarrow f(-c)+f(0)=f(c)-c
          simp only [h1, mul_zero, zero_add, neg_zero, sub_neg_eq_add] at h31
          --\Longrightarrow f(c)=2 c$.
          calc
            _ = f c + -c + c := by ring
            _ = c + c := by rw [← h31]
            _ = _ := by ring
        --4. $x=0, y=c
        have h4 : f (c ^ 2 - c) = c := by
          have h41 : P 0 c := h 0 c
          unfold P at h41
          --\Longrightarrow f(c)+f(-c)=f\left(c^{2}-c\right)+c
          simp only [h3, zero_mul, zero_add, h1, add_zero] at h41
          --\Longrightarrow f\left(c^{2}-c\right)=c$.
          calc
            _ = f (c * c - c) + c - c := by ring_nf
            _ = 2 * c - c := by rw [← h41]
            _ = _ := by ring
        --5. $x=-c, y=c^{2}-c
        have h5 : (c = 0) ∨ (c = 1) := by
          have h51 : P (-c) (c ^ 2 - c) := h (-c) (c ^ 2 - c)
          unfold P at h51
          --\Longrightarrow f(-c)+f(0)=f\left(c-c^{2}\right)+c^{2}-c
          simp only [h4, neg_mul, h1, neg_zero, mul_zero, zero_sub, neg_sub, h2, add_sub_cancel] at h51
          have h52 : f (-(c * c) + (c ^ 2 - c)) = 0 := by
            rw [← h1]
            ring_nf
          simp only [h52, zero_add] at h51
          --\Longrightarrow c=c^{2} \Longrightarrow c=0$ or 1.
          exact eq_zero_or_one_of_sq_eq_self (id (Eq.symm h51))
        cases' h5 with h5a h5b
        · --Suppose that $c=0$.
          --Let $f(-1)=d+1$.
          let d := f (-1) - 1
          --We make the following substitutions in the initial equation:
          have h0 : f 0 = 0 := h5a
          --1. $x=0
          have ha1 : ∀ (y : ℝ), y - f y = - f (-y) := by
            intro y
            have ha11 : P 0 y := h 0 y
            unfold P at ha11
            --\Longrightarrow f(y)+f(0)=f(-y)+y
            simp only [zero_mul, zero_add, h0, neg_zero, add_zero, mul_zero, zero_sub] at ha11
            --\Longrightarrow y-f(y)=-f(-y)$ for any $y \in \mathbb{R}$.
            simp only [ha11, sub_add_cancel_right]
          --2. $y=0
          have ha2 : ∀ (x : ℝ), f (- f x) = 0 := by
            intro x
            have ha21 : P x 0 := h x 0
            unfold P at ha21
            --\Longrightarrow f(0)+f(-f(x))=f(0)
            simp only [h0, mul_zero, add_zero, zero_add, zero_mul, sub_self] at ha21
            --\Longrightarrow f(-f(x))=0$ for any $x \in \mathbb{R}$.
            exact ha21
          --3. $x=-1
          have ha3 : ∀ (y : ℝ), f (d * y) = -y := by
            intro y
            have ha31 : P (-1) y := h (-1) y
            unfold P at ha31
            --\Longrightarrow f(y-f(y))+0=f(d y)+y
            simp only [neg_mul, one_mul, ha2, add_zero] at ha31
            nth_rw 1 [add_comm, ] at ha31
            rw [← sub_eq_add_neg, ha1, ha2] at ha31
            have hd : y * f (-1) - y = d * y := by
              ring
            rw [← hd]
            --\Longrightarrow f(d y)=-y+f(-f(-y))=-y$ for any $y \in \mathbb{R}$.
            exact eq_neg_of_add_eq_zero_left (id (Eq.symm ha31))
          --Thus, for any $x \in \mathbb{R}$ we have $f(x)=f(-f(d x))=0$.
          by_cases hd0 : d = 0
          --However, this function does not satisfy the initial equation.
          · simp only [hd0, zero_mul, h0] at ha3
            absurd ha3
            simp only [zero_eq_neg, not_forall]
            use 1
            norm_num
          · push_neg at hd0
            have hfd : ∀ (a : ℝ), f a = -(d⁻¹ * a) := by
              intro a
              have dinv : d * d⁻¹ = 1 := by
                exact CommGroupWithZero.mul_inv_cancel d hd0
              have hay : a = d * (d⁻¹ * a) := by
                rw [← mul_assoc, dinv, one_mul]
              nth_rw 1 [hay, ha3]
            let k := -d⁻¹
            have hfk : ∀ (a : ℝ), f a = k * a := by
              intro a
              rw [hfd]
              ring
            absurd h
            push_neg
            use 1, 0
            simp only [hfk, mul_zero, add_zero, mul_one, mul_neg, zero_add, zero_mul, sub_self, ne_eq, neg_eq_zero, mul_eq_zero, or_self]
            push_neg
            show -d⁻¹ ≠ 0
            simp only [ne_eq, neg_eq_zero, inv_eq_zero, hd0, not_false_eq_true]
        · --Suppose that $c=1$.
          --We take $x=0$ in the initial equation:
          have h0 : f 0 = 1 := h5b
          intro x
          have hb1 : P 0 x := h 0 x
          unfold P at hb1
          --$$ f(y)+f(-c)=f(0)+y
          have hneg1 : f (-1) = 0 := by
            rw [h5b] at h1
            exact h1
          simp only [zero_mul, zero_add, h0, hneg1, add_zero, mul_one, sub_self] at hb1
          --\Longrightarrow f(y)=y+1 $$ for any $y \in \mathbb{R}$.
          rw [hb1, add_comm]
      · --The function satisfies the initial equation.
        intro h x y
        rw [h, h, h, h, h]
        ring
      --Answer: $\quad f(x) \equiv x+1$.