#[
Copyright (C) 2017 Xiao-Yong Jin

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject
to the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR
ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF
CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
]#

##[

This module implements Chebyshev polynomial approximation to an
interval of a function.  The approximation works for a single
variable, and also for large scale sparse matrix operations as
well.

User has to define a set of operations, sepcifically, `apply`,
`assign`, and `newOneOf`, to be able to use the interface.  When
`concept` in Nim matures, we will use `concept` to enforce those.

See the end of the source code of this module for examples of use
cases.

]##

import math

type Chebyshev* = object    ## Parameters for Chebyshev approximation.
  coef*:seq[float]          ## Coefficients.
  center*, halfwidth*:float ## Center and half width of the approximation interval.
  degree*:int               ## Degree of the approximation.

template newChebyshev*(ab:Slice[float], n:int, fx:untyped):Chebyshev =
  ## Create a `Chebyshev` object with computed coefficients, given
  ## the interval as in [`a`, `b`], maximum degree `n`, and the function,
  ## `fx` given as an expression of type `float`, which uses `x` as
  ## the parameter of type `float`.
  let
    inv = 1.0/float(n+1)
    c = 0.5*(ab.b+ab.a)
    h = 0.5*(ab.b-ab.a)
  var
    z = Chebyshev(coef:newseq[float](n+1), center:c, halfWidth:h, degree:n)
    f = newseq[float](n+1)
  for i in 0..n:
    let x {.inject.} = c+h*cos(PI*(0.5+i.float)*inv)
    f[i] = fx
  let s = 2.0*inv
  for j in 0..n:
    var y = 0.0
    for i in 0..n: y += f[i]*cos(PI*j.float*(0.5+i.float)*inv)
    z.coef[j] = s*y
  z

#[ XXX: fix concept
type
  Operand = concept od
    # apply(Operator,od,od)
    newOneOf(od)
    #assign(var od,od)
  Operator = concept op
    apply(op,var Operand,Operand)
]#

template applyScaled(op:typed,c,ih:typed,a:typed,b:typed) =
  # a <- (x-c)/h * b = ih * (x*b - c*b)
  mixin `*`, apply, assign
  op.apply(a,b)
  a.assign(ih*(a-c*b))

# We use a template to avoid problems with the type of `res`.
# While non-var type works for `res` containing `ptr` or `ref`
# types, `res` requires a var type for simple object.
template apply*(chebyshev:Chebyshev,
                res:typed, op:typed, arg:typed) =
  ## Apply the `chebyshev` approximation of an `Operator`, `op`, on
  ## an argument `arg`.  The return type is the same as the `arg`.
  ## A `proc` `apply` must be defined for `op`, as
  ## `op.apply(output,input)`.
  mixin `*`, `+=`, apply, assign, newOneOf
  var t = [newOneOf res, newOneOf res]
  let
    c = chebyshev.center
    ih = 1.0/chebyshev.halfWidth
  for i in countdown(chebyshev.degree,1):
    let
      j = i and 1
      k = j xor 1
    op.applyScaled(c,ih,res,t[j])
    t[k].assign(2.0*res-t[k]+chebyshev.coef[i]*arg)
    #echo i," ",t[j]," ",t[k]
  let
    j = chebyshev.degree and 1
    k = j xor 1
  op.applyScaled(c,ih,res,t[j])
  res += 0.5*chebyshev.coef[0]*arg-t[k]

template chebyshevT*(res:typed, n:int, op:typed, arg:typed) =
  ## Apply the Chebyshev polynomial of the first kind with degree, `n`,
  ## of the operator `op` to the operand `arg`, and save the result in
  ## `res`.
  mixin apply, assign, newOneOf
  if 0 == n:
    res.assign arg
  elif 1 == n:
    op.apply(res, arg)
  else:
    var t = [newOneOf res, newOneOf res]
    t[0].assign arg
    op.apply(t[1], arg)
    for i in 2..<n:
      # T_n+1 = 2 x T_n - T_n-1
      let j = i and 1
      op.apply(res, t[j xor 1])
      t[j].assign(2.0*res - t[j])
    let j = n and 1
    op.apply(res, t[j xor 1])
    res.assign(2.0*res - t[j])

when isMainModule:
  import unittest
  var CT = 1e-12
  proc `~`(a,b:float):bool = abs(a-b)<CT*max(abs(a),abs(b))
  # For a float
  type F = object
    v:float
  # Operations for a float
  proc assign(z:var float, x:float) = z = x
  proc apply(o:F, z:var float, x:float) = z = o.v*x
  proc newOneOf(x:float):float = 0.0
  # For a matrix or an operator
  type
    V = object
      v:array[2,float]
    M = object
      v:array[2,V]
  # Operations for an operator
  proc assign(z:var V, x:V) = z = x
  proc apply(m:M, z:var V, x:V) =
    z.v[0] = m.v[0].v[0]*x.v[0] + m.v[0].v[1]*x.v[1]
    z.v[1] = m.v[1].v[0]*x.v[0] + m.v[1].v[1]*x.v[1]
  proc newOneOf(x:V):V = V(v:[0.0,0.0])
  proc `*`(x:float, y:V):V = V(v:[x*y.v[0],x*y.v[1]])
  proc `+`(x:V, y:V):V = V(v:[x.v[0]+y.v[0],x.v[1]+y.v[1]])
  proc `-`(x:V, y:V):V = V(v:[x.v[0]-y.v[0],x.v[1]-y.v[1]])
  proc `+=`(x:var V, y:V) = x = x+y
  # Operations for a matrix
  proc assign(z:var M, x:M) = z = x
  proc apply(m:M, mm:var M, x:M) =
    for i in 0..1:
      mm.v[i].v[0] = m.v[i].v[0] * x.v[0].v[0] + m.v[i].v[1] * x.v[1].v[0]
      mm.v[i].v[1] = m.v[i].v[0] * x.v[0].v[1] + m.v[i].v[1] * x.v[1].v[1]
  proc newOneOf(x:M):M = M(v:[V(v:[0.0,0.0]),V(v:[0.0,0.0])])
  proc `+`(x:M, y:float):M = M(v:[V(v:[x.v[0].v[0]+y,x.v[0].v[1]]),V(v:[x.v[1].v[0],x.v[1].v[1]+y])])
  proc `-`(x:float, y:M):M = M(v:[V(v:[x-y.v[0].v[0],-y.v[0].v[1]]),V(v:[-y.v[1].v[0],x-y.v[1].v[1]])])
  proc `+`(x:M, y:M):M = M(v:[x.v[0]+y.v[0], x.v[1]+y.v[1]])
  proc `-`(x:M, y:M):M = M(v:[x.v[0]-y.v[0], x.v[1]-y.v[1]])
  proc `*`(x:float, y:M):M = M(v:[x*y.v[0],x*y.v[1]])
  proc `+=`(x:var M, y:M) =
    x = x+y
  suite "Approximating log2(x)":
    let
      n = 6
      d = 64
      a = 1.0
      b = 2.0
      cheby = newChebyshev(a..b, n, log2(x))
    const c = [
      1.086213212662343,
      0.4950546725340528,
      -0.04246897663286743,
      0.004857681976391591,
      -0.0006250785977392065,
      8.57567965446282e-05,
      -1.199635485614965e-05]
    test "Coefficients":
      for i in 0..n:
        #echo "c ",i," = ",cheby.coef[i]
        check c[i] ~ cheby.coef[i]
    test "Approximation of a float":
      for j in 0..d:
        let
          x = a+j.float*(b-a)/d.float
          o = F(v:x)
        var y:float
        cheby.apply(y, o, 1.0)
        #echo "log2 ",x," = ",log2(x)," ~ ",y
        check abs(log2(x) - y)<3e-6
    let
      m = M(v:[V(v:[1.64,-0.48]),V(v:[-0.48,1.36])])
      v1 = V(v:[0.8,-0.6])
      v2 = V(v:[0.6,0.8])
    var y1,y2,z1,z2:V
    CT = 5e-6
    test "Approximation of a matrix":
      var mm:M
      cheby.apply(mm, m, 1.0)
      # echo mm.v[0].v[0]," ",mm.v[0].v[1]
      # echo mm.v[1].v[0]," ",mm.v[1].v[1]
      check mm.v[0].v[0] ~ 0.64
      check mm.v[0].v[1] ~ -0.48
      check mm.v[1].v[0] ~ -0.48
      check mm.v[1].v[1] ~ 0.36
      mm.apply(y1, v1)
      # echo y1.v[0]," ",y1.v[1]
      check y1.v[0] ~ 0.8
      check y1.v[1] ~ -0.6
      mm.apply(y2, v2)
      # echo y2.v[0]," ",y2.v[1]
      check abs(y2.v[0]) < 2e-6
      check abs(y2.v[1]) < 2e-6
    test "Approximation of an operator":
      cheby.apply(z1, m, v1)
      # echo z1.v[0]," ",z1.v[1]
      check z1.v[0] ~ 0.8
      check z1.v[1] ~ -0.6
      cheby.apply(z2, m, v2)
      # echo z2.v[0]," ",z2.v[1]
      check abs(z2.v[0]) < 2e-6
      check abs(z2.v[1]) < 2e-6
    test "Operator reproduce explicit matrix results":
      CT = 1e-14
      check y1.v[0] ~ z1.v[0]
      check y1.v[1] ~ z1.v[1]
      CT = 1e-8
      check y2.v[0] ~ z2.v[0]
      check y2.v[1] ~ z2.v[1]
  suite "Check chebyshevT":
    const T = [
      (n:60, x:2.0/3.0, v:0.980336300429690880),
      (n:61, x:1.0/3.0, v:0.9524252797925860546),
      (n:100, x:5.0/3.0, v:2.576887603660056655e47),
      (n:150, x:(-11.0)/7.0, v:2.456214171678742772e66),
      (n:151, x:1.001, v:428.04008973052097),
      (n:256, x:(-1.001), v:46843.475917840731),
      (n:16384, x:(-11.0)/13.0, v:(-0.5868893295919932))]
    var y:float
    CT = 1e-12
    for x in T:
      y.chebyshevT(x.n, F(v:x.x), 1.0)
      test($x & ": " & $y):
        check y ~ x.v
