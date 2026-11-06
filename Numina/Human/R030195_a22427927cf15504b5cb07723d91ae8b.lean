import Mathlib

/- From a sequence of integers $(a, b, c, d)$ each of the sequences

$$
(c, d, a, b),(b, a, d, c),(a+n c, b+n d, c, d),(a+n b, b, c+n d, d),
$$

for arbitrary integer $n$ can be obtained by one step. Is it possible to obtain $(3,4,5,7)$ from $(1,2,3,4)$ through a sequence of such steps?

## Solutions -/
theorem number_theory_605107 : ¬ (∃ a b c d : ℕ → ℝ, (a 0 = 1 ∧ b 0 = 2 ∧ c 0 = 3 ∧ d 0 = 4) ∧ 
(∀ n : ℕ, (a (n+1) = c n ∧ b (n+1) = d n ∧ c (n+1) = a n ∧ d (n+1) = b n) 
∨ (a (n+1) = b n ∧ b (n+1) = a n ∧ c (n+1) = d n ∧ d (n+1) = c n) 
∨ (a (n+1) = a n + n * c n ∧ b (n+1) = b n + n * d n ∧ c (n+1) = c n ∧ d (n+1) = d n) 
∨ (a (n+1) = a n + n * b n ∧ b (n+1) = b n ∧ c (n+1) = c n + n * d n ∧ d (n+1) = d n) ) ∧ 
(∃ m : ℕ, a m = 3 ∧ b m = 4 ∧ c m = 5 ∧ d m =7)
) := by 
  intro h
  obtain ⟨a,b,c,d, h0, h, htar⟩ := h
  obtain ⟨ha0, hb0, hc0, hd0⟩ := h0
  -- We prove that if there is such a sequence, then |a n * d n - b n * c n| is the same for all n.
  -- Since |3*7-4*5|=1 and |1*4-2*3|=2, we have these cannot be equal so it's impossible.
  have cla : ∀ n : ℕ, |a n * d n - b n * c n| = 2 := by
    intro n
    induction' n with n hn

    simp [ha0,hb0,hc0,hd0]; 
    norm_num
  
    specialize h n
    rcases h with h | h | h |h
    
    simp [h]
    have : |c n * b n - d n * a n| = |a n * d n - b n * c n|  := by 
      refine abs_eq_abs.mpr ?_;
      right; 
      linarith
    linarith

    simp [h]
    have : |b n * c n - a n * d n| = |a n * d n - b n * c n|  := by 
      refine abs_eq_abs.mpr ?_;
      right; 
      linarith
    linarith

    simp [h]; ring_nf
    have : |a n * d n - c n * b n| = |a n * d n - b n * c n|  := by 
      refine abs_eq_abs.mpr ?_;
      left
      nlinarith
    linarith

    simp [h]; ring_nf
    assumption


  obtain ⟨m, ham,hbm,hcm,hdm⟩ := htar
  have : |a m * d m - b m * c m| = 2 := by apply cla
  rw [ham, hbm, hcm, hdm] at this
  norm_num at this;


