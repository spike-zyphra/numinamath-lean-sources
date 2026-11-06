import Mathlib

/- 39th Putnam 1978 Problem A4 A binary operation (represented by multiplication) on S has the property that (ab)(cd) = ad for all a, b, c, d. Show that: (1) if ab = c, then cc = c; (2) if ab = c, then ad = cd for all d. Find a set S, and such a binary operation, which also satisfies: (A) a a = a for all a; (B) ab = a ≠ b for some a, b; (C) ab ≠ a for some a, b. -/
theorem algebra_133655 {S : Type} {f : S → S → S}
    (h : ∀ a b c d, f (f a b) (f c d) = f a d) :
    (∀ a b c, f a b = c → f c c = c) ∧
    (∀ a b c, f a b = c → ∀ d, f a d = f c d) ∧
    ∃ S : Type, ∃ f : S → S → S,
      (∀ a, f a a = a) ∧
      ∃ a b, f a b = a ∧ a ≠ b ∧
      ∃ a b, f a b ≠ a := by
    constructor
    --the first claim is true because from the hypotheses (ab)(ab)=(ab) and ab = c then cc = c
    · intro a b c hfab
      specialize h a b a b
      rw[hfab] at h
      exact h
    · constructor
      --the second claim is true because from the hypotheses (cc)(cd) = cd
      --from the first claim cc = c implies c(cd)=cd
      --and from ab=c we have (ab)(cd)=cd which from the hypotheses again yields the claim
      · intro a b c hfabc d
        have one : f c c = c := by 
          specialize h a b a b
          rw[hfabc] at h
          exact h
        have id1 : f c (f c d) = f a d := by
          specialize h a b c d
          rw[hfabc] at h
          exact h
        nth_rw 1 [← one] at id1
        rw[h c c c d] at id1
        exact symm id1
      --we use as S the model of ℤ₂ × ℤ₂ and as a multiplication the projection on the first component of the first factor and second component of the second factor. 
      · use Bool × Bool
        use fun ((a, b) : Bool × Bool) ((c, d) : Bool × Bool) => (a, d)
        --the required properties are just a simple logic check
        simp