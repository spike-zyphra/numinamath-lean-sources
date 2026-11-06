import Mathlib
set_option maxRecDepth 5000 -- we need this to factorise 244
theorem aime_735 {x y : ℕ} (h : x^2 + 84*x + 2008 = y^2) : x + y = 80 := by
  -- complete the square
  have step1 : y^2 = (x + 42)^2 + 244 := calc
    y^2 = x^2 + 84*x + 2008 := h.symm
    _ = (x + 42)^2 + 244 := by linarith

  -- rearrange
  have step2 : y^2 - (x + 42)^2 = 244 := by rw [step1]; omega

  -- factorise the difference of squares
  have step3 : (y + (x + 42)) * (y - (x + 42)) = 244 := by rw [← Nat.sq_sub_sq,← step2]

  -- factorise the right-hand side
  have step4 : Nat.divisorsAntidiagonal 244 = {(1,244), (2,122), (4,61), (61,4), (122,2), (244,1) } := by
    rw [← @Nat.map_div_right_divisors (244 : ℕ)]
    decide

  -- match the divisors
  have step5 : (y + (x + 42), (y - (x + 42))) ∈ Nat.divisorsAntidiagonal 244 :=
   Nat.mem_divisorsAntidiagonal.mpr ⟨step3,by decide⟩

  -- replace the divisors by the known list
  rw [step4] at step5
  repeat rw [Finset.mem_insert] at step5      
  rw [Finset.mem_singleton] at step5

  -- we now do a case-by-case analysis
  cases step5 with
  | inl a => rw [Prod.mk.injEq] at a; linarith -- impossible by inequality
  | inr b => cases b with
    | inl a => rw [Prod.mk.injEq] at a; linarith -- impossible by inequality
    | inr b => cases b with
      | inl a => rw [Prod.mk.injEq] at a; linarith -- impossible by inequality
      | inr b => cases b with
        | inl a => rw [Prod.mk.injEq] at a; omega -- impossible by parity
        | inr b => cases b with
          | inl a => rw [Prod.mk.injEq] at a; linarith -- the correct solution
          | inr a => rw [Prod.mk.injEq] at a; omega -- impossible by parity