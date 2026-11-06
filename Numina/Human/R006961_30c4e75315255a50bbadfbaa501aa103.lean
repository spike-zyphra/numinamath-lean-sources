import Mathlib

/-If $Q = 11-5i$, $E = 11+5i$, and $D = 2i$, find $Q\cdot E \cdot D$.-/

theorem algebra_20147 {Q E D : ℂ} (hQ : Q = 11 - 5 * .I) (hE : E = 11 + 5 * .I)

    (hD : D = 2 * .I) : Q * E * D = 292 * .I := by
    --\begin{align*}QED &= (11-5i)(11+5i)2i\\&=2i(121-(5i)^2)\\&=2i(121+25)\\&=\boxed{292i}.\end{align*}
    rw[hQ]; rw[hE]; rw[hD]
    ring_nf
    rw [show Complex.I ^ 3 = Complex.I ^ 2 * Complex.I  by ring_nf]
    rw [Complex.I_sq]
    ring_nf