import Mathlib

/-- The numbers $\(a\)$ and $\(b\)$ are such that the polynomial $\(x^{4} - x^{3} + x^{2} + a x + b\)$ is the square of some other polynomial. Find $\(b\)$.-/
theorem algebra_4035
  (a b : ℝ)
  (h : ∃p q r : ℝ, ∀ x : ℝ, x^4 - x^3 + x^2 + a * x + b = (p*x^2 + q * x + r)^2) :
  b = 9 / 64 := by
  -- Because of the degree of $x^4 - x^3 + x^2 + a * x + b$ is 4, it could only be
  -- the square of polynomial which degree is 2. And assume the polynomial is 
  --  $p*x^2 + q * x + r$. 
  obtain ⟨p ,q, r, h_eq⟩ := h
  -- replace $x$ by 0 in $x^4 - x^3 + x^2 + a * x + b = (p*x^2 + q * x + r)^2$.
  have h0:= h_eq 0
  ring_nf at h0
  -- replace $x$ by 1 in $x^4 - x^3 + x^2 + a * x + b = (p*x^2 + q * x + r)^2$.
  have h1:= h_eq 1
  ring_nf at h1
  -- replace $x$ by -1 in $x^4 - x^3 + x^2 + a * x + b = (p*x^2 + q * x + r)^2$.
  have hm1:= h_eq (-1)
  ring_nf at hm1
  -- replace $x$ by 2 in $x^4 - x^3 + x^2 + a * x + b = (p*x^2 + q * x + r)^2$.
  have h2:= h_eq 2
  ring_nf at h2
  -- replace $x$ by -2 in $x^4 - x^3 + x^2 + a * x + b = (p*x^2 + q * x + r)^2$.
  have hm2:= h_eq (-2)
  ring_nf at hm2

  rw[h0]
  rw[h0] at h1
  rw[h0] at hm1
  rw[h0] at h2
  rw[h0] at hm2
  -- Because the corresponding coefficients are equal, we get $p^2=1$, $2pq=-1$ and $q^2+2*p*r=1$.
  have hp:p^2=1:=by nlinarith
  have hpq:2*p*q=-1 :=by nlinarith
  have hpqr:q^2+2*p*r=1:= by nlinarith
  simp at hp
  -- solve for $p,q,r$. 
  cases hp with
  | inl h1 => rw[h1] at hpq
              rw[h1] at hpqr
              simp at hpq
              have hr:r=(1-q^2)/2:= by field_simp at hpqr;field_simp;rw[← hpqr];ring
              rw [hr]
              have hq:q=-(1/2):= by field_simp;linarith
              rw[hq]
              ring
  | inr h1 => rw[h1] at hpq
              rw[h1] at hpqr
              simp at hpq
              have hr:r=-(1-q^2)/2:= by field_simp at hpqr;field_simp;rw[← hpqr];ring
              rw [hr]
              have hq:q=(1/2):= by field_simp;linarith
              rw[hq]
              ring
