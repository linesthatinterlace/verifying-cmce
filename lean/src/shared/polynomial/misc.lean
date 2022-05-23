import data.polynomial.derivative

namespace polynomial

open_locale polynomial
theorem bernoulli_rule {R : Type*} [comm_ring R] {p q : R[X]} {x : R} (h : p.is_root x) :
(p*q).derivative.eval x = p.derivative.eval x * q.eval x :=
begin
  rw is_root.def at h,
  simp only [is_root.def, h, derivative_mul, eval_add, eval_mul, zero_mul, add_zero]
end

end polynomial