import Mathlib

/- Let $k$ be a positive integer. Suppose $k$ truckloads are delivered to a supermarket, and each truckload contains a quantity of eggs equivalent to 2 gross, 3 dozen, and 7 eggs. (A gross is 12 dozen, and a dozen is 12 eggs, so each truckload contains $2 \cdot 12^2 + 3 \cdot 12 + 7 = 331$ eggs.) Calculate the total number of eggs delivered, expressing the result in the form of $G_k$ gross, $D_k$ dozen, and $E_k$ individual eggs, where $0 \le D_k < 12$ and $0 \le E_k < 12$. Show that $G_k = \lfloor (331k)/144 \rfloor$, $D_k = \lfloor ((331k) \pmod{144})/12 \rfloor$, and $E_k = ((331k) \pmod{12})$. -/
theorem number_theory_641346 (k : ℕ) (kpos : 0 < k) :
    let total_eggs := k * 2 * 12^2 + k * 3 * 12 + k * 7
    let G := total_eggs / 144
    let D := (total_eggs % 144) / 12
    let E := total_eggs % 12
    G = 331 * k / 144 ∧ D = (331 * k % 144) / 12 ∧ E = (331 * k) % 12 :=
 by
  constructor
  <;> omega
