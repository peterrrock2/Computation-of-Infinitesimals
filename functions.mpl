
with(LinearAlgebra);



makegenM := overload([proc(d::integer, y::anything) local M, i, j, f; option overload; description "construct the sample matrix M of dimension dim"; M := Matrix(d); if d = 1 then return Matrix([[1]]); end if; M(1 .. (), 1) := Vector(d, fill = 1); for i to d do for j from 2 to d do M(i, j) := x[y + i - 1]^(j - 1); end do; end do; f(y) := M; return f(y); end proc, proc(d::integer) local M, i, j, f, y; option overload; description "construct the sample matrix M of dimension dim"; y := 0; M := Matrix(d); if d = 1 then return Matrix([[1]]); end if; M(1 .. (), 1) := Vector(d, fill = 1); for i to d do for j from 2 to d do M(i, j) := x[y + i - 1]^(j - 1); end do; end do; f(y) := M; return f(y); end proc]);
NULL;
NULL;
makegenMy := overload([proc(d::integer, y::anything) local M, i, j, f; option overload; description "construct the sample matrix M of dimension dim"; M := Matrix(d); if d = 1 then return Matrix([[1]]); end if; M(1 .. (), 1) := Vector(d, fill = 1); for i to d do for j from 2 to d do M(i, j) := y[x + i - 1]^(j - 1); end do; end do; f(x) := M; return f(x); end proc, proc(d::integer) local M, i, j, f, x; option overload; description "construct the sample matrix M of dimension dim"; x := 0; M := Matrix(d); if d = 1 then return Matrix([[1]]); end if; M(1 .. (), 1) := Vector(d, fill = 1); for i to d do for j from 2 to d do M(i, j) := y[x + i - 1]^(j - 1); end do; end do; f(x) := M; return f(x); end proc]);
NULL;
NULL;
NULL;
makeredM := overload([proc(d::integer, y::anything) local M, i, j, f; option overload; description "construct the sample matrix M of dimension dim"; M := Matrix(d); if d = 1 then return Matrix([[1]]); end if; M(1 .. (), 1) := Vector(d, fill = 1); for i to d do for j from 2 to d do M(i, j) := (x[y + i - 1] - x[y])^(j - 1); end do; end do; f(y) := M; return f(y); end proc, proc(d::integer) local M, i, j, f, y; option overload; description "construct the sample matrix M of dimension dim"; y := 0; M := Matrix(d); if d = 1 then return Matrix([[1]]); end if; M(1 .. (), 1) := Vector(d, fill = 1); for i to d do for j from 2 to d do M(i, j) := (x[y + i - 1] - x[y])^(j - 1); end do; end do; f(y) := M; return f(y); end proc]);
NULL;NULL;


makefElem := overload([proc(k::integer, m::integer, f::integer, y::anything) local M, i, j, l, n; option overload; n := m + 1; if n < k or k < 0 then return 0; elif k = 0 then return 1; end if; M := Matrix(k); for i to k - 1 do M(i, i + 1) := i; end do; for i to k do for j from 0 to k - i do if m < f then M(i + j, j + 1) := sum(x[y + l]^i, l = 0 .. n - 1); else M(i + j, j + 1) := sum(x[y + l]^i, l = 0 .. n - 1) - x[y + f]^i; end if; end do; end do; return LinearAlgebra:-Determinant(M)/k!; end proc, proc(k::integer, m::integer, f::integer) local M, i, j, n, l, y; option overload; y := 0; n := m + 1; if n < k or k < 0 then return 0; elif k = 0 then return 1; end if; M := Matrix(k); for i to k - 1 do M(i, i + 1) := i; end do; for i to k do for j from 0 to k - i do if m < f then M(i + j, j + 1) := sum(x[y + l]^i, l = 0 .. n - 1); else M(i + j, j + 1) := sum(x[y + l]^i, l = 0 .. n - 1) - x[y + f]^i; end if; end do; end do; return LinearAlgebra:-Determinant(M)/k!; end proc]);



replaceCol := proc(M::Matrix, cnum::integer, col::Matrix)::Matrix; description "replace column cnm with col in matrix M"; if cnum = 1 then return <col | M(1 .. (), cnum + 1 .. ())>; elif cnum = ColumnDimension(M) then return <M(1 .. (), 1 .. cnum - 1) | col>; else return <M(1 .. (), 1 .. cnum - 1) | col | M(1 .. (), cnum + 1 .. ())>; end if; end proc;



evalCol := overload([proc(u, d::integer, y::anything)::Matrix; local i; option overload; description "make column that is the points evaluated at u"; return Transpose(Matrix([seq(u(x[y + i - 1]), i = 1 .. d)])); end proc, proc(u, d::integer)::Matrix; local i, y; option overload; description "make column that is the points evaluated at u"; y := 0; return Transpose(Matrix([seq(u(x[y + i - 1]), i = 1 .. d)])); end proc]);


makesiglk := overload([proc(l, k, y) local i, mesum, deter, r, j; option overload; deter := LinearAlgebra:-Determinant(makegenM(l + 1)); mesum := 0; for i from 0 to l do mesum := mesum + makefElem(k, l + 1, i, y)*u(x[y + i])/(product(x[y + i] - x[r + y], r = i + 1 .. l)*product(x[y + i] - x[y + j], j = 0 .. i - 1)); end do; return (-1)^k*simplify(deter*mesum); end proc, proc(l, k) local i, mesum, deter, r, j; option overload; deter := LinearAlgebra:-Determinant(makegenM(l + 1)); mesum := 0; for i from 0 to l do mesum := mesum + makefElem(k, l + 1, i)*u(x[i])/(product(x[i] - x[r], r = i + 1 .. l)*product(x[i] - x[j], j = 0 .. i - 1)); end do; return (-1)^k*simplify(deter*mesum); end proc]);



makeulk := overload([proc(ll, kk, y) local i, mesum, r, j, l, k; option overload; if ll = 0 then return u(x[y]); end if; l := ll + 1; k := kk + 1; mesum := 0; for i from 0 to l - 1 do mesum := mesum + makefElem(ll - kk, ll, i, y)*u(x[y + i])/(product(x[y + i] - x[y + r], r = i + 1 .. l - 1)*product(x[y + i] - x[j + y], j = 0 .. i - 1)); end do; return ll!*(-1)^(ll - kk)*mesum; end proc, proc(ll, kk) local i, mesum, r, j, l, k, y; option overload; if ll = 0 then return u(x[0]); end if; y := 0; l := ll + 1; k := kk + 1; mesum := 0; for i from 0 to l - 1 do mesum := mesum + makefElem(ll - kk, ll, i, y)*u(x[y + i])/(product(x[y + i] - x[y + r], r = i + 1 .. l - 1)*product(x[y + i] - x[y + j], j = 0 .. i - 1)); end do; return ll!*(-1)^(ll - kk)*mesum; end proc]);

NULL;
ulk := overload([proc(kk, ll, y) local i, mesum, r, j, l, k; option overload; if ll = 0 then return u(x[y]); end if; l := ll + 1; k := kk + 1; mesum := 0; for i from 0 to l - 1 do mesum := mesum + makefElem(ll - kk, ll, i, y)*u(x[y + i])/(product(x[y + i] - x[y + r], r = i + 1 .. l - 1)*product(x[y + i] - x[j + y], j = 0 .. i - 1)); end do; return ll!*(-1)^(ll - kk)*mesum; end proc, proc(kk, ll) local i, mesum, r, j, l, k, y; option overload; if ll = 0 then return u(x[0]); end if; y := 0; l := ll + 1; k := kk + 1; mesum := 0; for i from 0 to l - 1 do mesum := mesum + makefElem(ll - kk, ll, i, y)*u(x[y + i])/(product(x[y + i] - x[y + r], r = i + 1 .. l - 1)*product(x[y + i] - x[y + j], j = 0 .. i - 1)); end do; return ll!*(-1)^(ll - kk)*mesum; end proc]);
NULL;



makexilk := overload([proc(ll, kk, y) local i, mesum, r, j, l, k; option overload; if kk = 0 then return xi(x[y]); end if; l := ll + 1; k := kk + 1; mesum := 0; for i from 0 to k - 1 do mesum := mesum + makefElem(0, ll, i, y)*ll*x[y + i]^(ll - 1)*xi(x[y + i])/(product(x[y + i] - x[y + r], r = i + 1 .. k - 1)*product(x[y + i] - x[j + y], j = 0 .. i - 1)); end do; return kk!*mesum; end proc, proc(ll, kk) local i, mesum, r, j, l, k, y; option overload; y := 0; if kk = 0 then return xi(x[y]); end if; l := ll + 1; k := kk + 1; mesum := 0; for i from 0 to k - 1 do mesum := mesum + makefElem(0, ll, i, y)*ll*x[y + i]^(ll - 1)*xi(x[y + i])/(product(x[y + i] - x[y + r], r = i + 1 .. k - 1)*product(x[y + i] - x[y + j], j = 0 .. i - 1)); end do; return kk!*mesum; end proc]);
NULL;
NULL;
xilk := overload([proc(ll, kk, y) local i, mesum, r, j, l, k; option overload; if kk = 0 then return xi(x[y]); end if; l := ll + 1; k := kk + 1; mesum := 0; for i from 0 to k - 1 do mesum := mesum + makefElem(0, ll, i, y)*ll*x[y + i]^(ll - 1)*xi(x[y + i])/(product(x[y + i] - x[y + r], r = i + 1 .. k - 1)*product(x[y + i] - x[j + y], j = 0 .. i - 1)); end do; return kk!*mesum; end proc, proc(ll, kk) local i, mesum, r, j, l, k, y; option overload; y := 0; if kk = 0 then return xi(x[y]); end if; l := ll + 1; k := kk + 1; mesum := 0; for i from 0 to k - 1 do mesum := mesum + makefElem(0, ll, i, y)*ll*x[y + i]^(ll - 1)*xi(x[y + i])/(product(x[y + i] - x[y + r], r = i + 1 .. k - 1)*product(x[y + i] - x[j + y], j = 0 .. i - 1)); end do; return kk!*mesum; end proc]);



makeflk := overload([proc(u, ll, kk, y) local i, mesum, r, j, l, k; option overload; if ll = 0 then return u(x[y]); end if; l := ll + 1; k := kk + 1; mesum := 0; for i from 0 to l - 1 do mesum := mesum + makefElem(ll - kk, ll, i, y)*u(x[y + i])/(product(x[y + i] - x[y + r], r = i + 1 .. l - 1)*product(x[y + i] - x[j + y], j = 0 .. i - 1)); end do; return ll!*(-1)^(ll - kk)*mesum; end proc, proc(u, ll, kk) local i, mesum, r, j, l, k, y; option overload; if ll = 0 then return u(x[0]); end if; y := 0; l := ll + 1; k := kk + 1; mesum := 0; for i from 0 to l - 1 do mesum := mesum + makefElem(ll - kk, ll, i, y)*u(x[y + i])/(product(x[y + i] - x[y + r], r = i + 1 .. l - 1)*product(x[y + i] - x[j + y], j = 0 .. i - 1)); end do; return ll!*(-1)^(ll - kk)*mesum; end proc]);




comhom := proc(lister, n) local mesum, i; if 1 < n then mesum := lister[1]^n; if 1 < nops(lister) then for i from 0 to n - 1 do mesum := mesum + lister[1]^i*comhom(lister[2 .. ()], n - i); end do; end if; return mesum; end if; if n = 1 then return sum(lister[k], k = 1 .. nops(lister)); end if; return 1; end proc;





xlist := proc(size, start) local i; return [seq(x[i], i = start .. start + size - 1)]; end proc;


NULL;
ddifer := proc(f, x, n, endv::integer, basev::integer, shift::integer, shiftf::integer) if endv - basev < n then printf("There is not enough distance between the end point, %g, and the basepoint, %g, to take the ddif, %g times", endv, basev, n); return 0; end if; if n = 1 then return (f(1 + shiftf) - f(shiftf))/(x[basev + endv + shift] - x[basev + shift]); else return (ddifer(f, x, n - 1, endv - 1, basev, shift + 1, 1 + shiftf) - ddifer(f, x, n - 1, endv - 1, basev, shift, shiftf))/(x[basev + endv + shift] - x[basev + shift]); end if; end proc;
NULL;
;
# 



mHom := proc(low, high, deg) local i, j; return coeff(product(add((x[i]*t)^j, j = 0 .. deg), i = low .. high), t, deg); end proc;
NULL;

NULL;
NULL;
NULL;
NULL;








