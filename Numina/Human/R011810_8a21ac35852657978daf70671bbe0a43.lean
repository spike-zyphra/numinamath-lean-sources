import Mathlib

/- $2. Given a ratio $a: b=c: d$.
(1) Prove: $a: b=(a+c):(b+d)$;
(2) The ratio $a: b=(a c):(b d)$ is also correct. Is this conclusion true? -/
theorem algebra_313382 :
    (∀ a b c d : ℝ, b ≠ 0 → d ≠ 0 → b + d ≠ 0 →
      a / b = c / d →
       a / b = (a + c) / (b + d)) ∧ ¬ (∀ a b c d : ℝ, b ≠ 0 → d ≠ 0 → b + d ≠ 0 →
      a / b = c / d → a / b = a * c / b * d) := by
    constructor 
    · intro a b c d hb hd hbd h 
      field_simp at h
      -- 2. (1) From $a d=b c$, we get $a(b+d)=b(a+c)$.
      have : a * (b + d) = b * (a + c) := by
        ring_nf 
        rw [h]
        ring 
      field_simp 
      -- Therefore, $a: b=(a+c):(b+d)$.
      rw [this]
      ring 
    · push_neg 
      -- If $a: b= c^{2} d \neq 1$, then, $a: b \neq(a c):(b d)$. 
      -- For example, $2: 1=4: 2$, but $2: 1 \neq 8: 2$. So $a: b=(a c):(b d)$ is not true.
      use 2, 1, 4, 2 
      norm_num 

