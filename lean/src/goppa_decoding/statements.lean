import data.polynomial.field_division
import data.zmod.basic
import algebra.char_p.two
import algebra.squarefree
import ring_theory.coprime.basic
import ring_theory.ideal.basic
import field_theory.splitting_field
import shared.coding_theory.hamming

namespace goppa_decoding
open_locale big_operators polynomial classical
open polynomial euclidean_domain

lemma checking_goppa_decoding_recieved_words_zmod2 (n t k : ℕ) {K : Type*} [fintype K] [field K] 
[char_p K 2] (α : fin n → K) (H : function.injective α) (A g : K[X])
(A_def : A = ∏ i : fin n, (X - C (α i)) ) (g_sf : squarefree g) (g_degree : g.degree = t)
(g_gcd : is_coprime g A) (B a b : K[X]) (h_ab : is_coprime a b) (h_a : degree a ≤ t)
(h_Aa : A ∈ ideal.span ({a} : set K[X])) (h_deg : (a*B - b*A).degree < (↑(n - 2*t) + degree a)) 
(h_bleh : ∀ i : fin n, g.eval (α i)^2 * (B.eval (α i)) / (A.derivative.eval (α i)) = 1 ∨
g.eval (α i)^2 * B.eval (α i) / (A.derivative.eval (α i)) = 0)
(e : fin n → zmod 2) (h_e : ∀ i, e i = if (a.eval (α i) = 0) then 0 else 1) :
↑(coding_theory.ham_wt e) = a.degree ∧
(∑ i : fin n, C (g.eval (α i)^2 * B.eval (α i) - zmod.cast (e i)) * (A / (X - C (α i)) )
∈ ideal.span ({g^2} : set K[X])) := sorry


end goppa_decoding

-- Might want that if two polynomials are coprime, they don't share roots, and what the roots of A are. If g and A don't share roots, I think it is true that they are coprime, but what do you need for this?
-- Need that integer degree...

