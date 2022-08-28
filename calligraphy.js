// node -i -e 'var c = require("./calligraphy.js")'
var quartic = require("quartic");
class Vec extends Array {
  constructor(v) {
    super();
    Object.assign(this, v);
  }
  map(f) {return new Vec(super.map(f));}
  slice(...args) {return new Vec(super.slice(...args));}
  toString() {
    return "⟨" + super.join(", ") + "⟩"
  }
}
class Curve extends Array {
  constructor(v) {
    super();
    Object.assign(this, v);
  }
  map(f) {return new Curve(super.map(f));}
  slice(...args) {return new Curve(super.slice(...args));}
  toString() {
    return '<' + this.join(" ") + '>';
  }
}
class Poly extends Array {
  constructor(v) {
    super();
    Object.assign(this, v);
  }
  map(f) {return new Poly(super.map(f));}
  slice(...args) {return new Poly(super.slice(...args));}
  toString() {
    if (!this.length) return "0";
    Poly.prime += 1;
    let cs = this.map(v => v.toString());
    Poly.prime -= 1;
    let vars = ["X", "Y", "Z"];
    return cs.reduce((r, v, i) => v ? (r[0] !== "0" || r[1] === "." ? r + " + " : "") + (v !== "1" ? (v.includes("+") ? "(" + v + ")" : v) + "*" : "")+(vars[Poly.prime]||"t_"+Poly.prime)+"^"+i : r);
  }
}
Poly.prime = 0;
const curveD = ps => new Curve(ps).map(p => new Vec(p));

const construct_like = (d, cs) => {
  if (!cs.length) return d;
  var p = cs[0].__proto__;
  if (p === Array.prototype || p === Number.prototype) {
    return d;
  }
  for (let c of cs) {
    if (p !== c.__proto__) {
      return d;
    }
  }
  return new p.constructor(d);
};

const zipWith = (f,d1,d2) => (cs1, cs2) => {
  var r = [];
  for (let i = 0; i < cs1.length || i < cs2.length; i += 1) {
    var v1 = i in cs1 ? cs1[i] : d1;
    var v2 = i in cs2 ? cs2[i] : d2;
    r.push(f(v1, v2));
  }
  return construct_like(r, [cs1, cs2]);
};

const map = f => vs => vs.map(f);

const compose = (...fs) => i => {
  var o = i;
  for (let f of fs.reverse()) {
    o = f(o);
  }
  return o;
};

const lift2 = (op, annihilate) => (vs1, vs2) => {
  if (vs2 === 0) return vs1;
  if (vs1 === 0) return vs2;
  if (typeof vs1 === 'number' && typeof vs2 === 'number')
    return op(vs1,vs2);
  return zipWith(lift2(op), 0, 0)(vs1, vs2);
};
const lift1 = op => (vs1) => {
  if (typeof vs1 === 'number')
    return op(vs1);
  return vs1.map(lift1(op));
};
const summate = vs1 => {
  if (typeof vs1 === 'number')
    return vs1;
  if (!vs1.length) return 0;
  return vs1.map(sum).reduce((a, b) => a+b);
};
const sum = vs1 => {
  if (!vs1.length) return 0;
  return vs1.reduce(add);
};
const add = lift2((v1,v2) => v1+v2);
const sub = (vs1, vs2) => add(vs1, mul(-1, vs2));
const mul = (c,cs) => lift1(v => c*v)(cs);
const muldot = (cs, css) => sum(zipWith((z, zs) => mul(z, zs))(cs, css));
const dot = (vs1, vs2) => summate(lift2((v1,v2) => mul(v1,v2), true)(vs1, vs2));
const dmul = (cs1, cs2) => cs1.map(c1 => mul(c1, cs2));
const pmul = (cs1, cs2) => sum(cs1.map((c1, i) => raise(i)(mul(c1, cs2))));

const transpose = vss => {
  var rss = [];
  for (let i in vss) {
    for (let j in vss[i]) {
      rss[j] = rss[j] || construct_like([], [vss]);
      rss[j][i] = vss[i][j];
    }
  }
  return construct_like(rss, [...vss]);
};
const transposed = f => compose(map(f), transpose);
const transposing = f => compose(transpose, map(f), transpose);
const bases = dim => {
  var zeros = [];
  for (let i = 0; i < dim; i += 1) zeros.push(0);
  return zeros.map((_, i) => new Vec(zeros.map((_, j) => +(i == j))));
};

const value = cs => t => cs.reduce((r, c, i) => r + c * Math.pow(t, i), 0);
const values = vcs => t => vcs.map(cs => value(cs)(t));
const EVAL = cvs => t => transposed(cs => value(cs)(t))(cvs);
const deriv = cs => cs.map((v, i) => i * v).slice(1);
const DERIV = transposing(deriv);

const raise = n => n <= 0 ? (cs => cs) : cs => raise(n-1)(N(cs));
const N = cs => construct_like([0].concat(cs), [cs]);
const Y = cs => sub(cs, N(cs));

const b = ps => {
  if (typeof ps === 'number') {
    return new Vec(bases(ps)).map(b);
  }
  // c.b(ps) === c.muldot(ps, c.b(ps.length))
  if (ps.length <= 1) return new Poly(ps);
  return add(Y(b(ps.slice(0, -1))), N(b(ps.slice(1))));
};
const B = transposing(b);
const curvature = (XX,YY,XXX,YYY) => {
  return (XX*YYY - YY*XXX)/Math.pow(XX*XX + YY*YY, 1.5);
};
const Bcurvature0 = ([b0,b1,b2,_]) => {
  let b21 = [b2[0]-b1[0],b2[1]-b1[1]];
  let d0 = [b1[0]-b0[0],b1[1]-b0[1]];
  let d0xb21 = d0[0]*b21[1] - d0[1]*b21[0];
  let delta = Math.sqrt(d0[0]*d0[0] + d0[1]*d0[1]);
  return (2/3)*d0xb21/Math.pow(delta, 3);
};
const Bcurvature1 = ([b0,b1,b2,b3]) => -Bcurvature0([b3,b2,b1,b0]);
const Bcurvature = C => t => {
  let [numer, denom] = Bcurvature_polys(C).map(p => value(p)(t));
  return numer/Math.pow(denom, 1.5);
};
const Bcurvature_polys = C => {
  let CC = DERIV(B(C));
  let XX = transpose(CC)[0];
  let YY = transpose(CC)[1];
  let CCC = DERIV(CC);
  let XXX = transpose(CCC)[0];
  let YYY = transpose(CCC)[1];
  return [sub(pmul(XX,YYY), pmul(YY,XXX)), add(pmul(XX,XX), pmul(YY,YY))];
};
const norm = v => Math.sqrt(v[0]*v[0] + v[1]*v[1]);
const normalize = v => {let n = norm(v); return [v[0]/n, v[1]/n]};
const cross2 = (v1,v2) => v1[0]*v2[1] - v1[1]*v2[0];
const solve_quartic = cs => {
  let rs = quartic(cs.slice().reverse());
  //console.log(cs);
  let rs2 = rs.filter(r => r.im === 0).map(r => r.re);
  //console.log(rs2.map(r => ([r, value(cs)(r)])));
  return rs2;
};
const fit = (f0,f1,d0,d1,k0,k1) => {
  d0 = normalize(d0); d1 = normalize(d1);
  let d0xd1 = cross2(d0, d1);
  let a = sub(f1, f0);
  let d0xa = cross2(d0, a);
  let axd1 = cross2(a, d1);
  //console.log({d0xd1, d0xa, axd1});
  let δs;
  if (d0xd1 === 0) {
    δs = [Math.sqrt((2/3)*(d0xa)/k0), Math.sqrt((2/3)*(axd1)/k1)];
  } else {
    // https://herbie.uwplse.org/
    /**/
    let ρs;
    //let R0 = (3/2)*(k0*axd1*axd1)/(d0xa*d0xd1*d0xd1);
    let R0 = 1.5 * (((axd1 / d0xa) / (d0xd1 / k0)) / (d0xd1 / axd1));
    //let R1 = (3/2)*(k1*d0xa*d0xa)/(axd1*d0xd1*d0xd1);
    let R1 = 1.5 * (((d0xa / axd1) / (d0xd1 / k1)) / (d0xd1 / d0xa));
    //console.log({ R0, R1 });
    let c0 = [1-R1, -1, 2*R1*R0, 0, -R1*R0*R0];
    let c1 = [1-R0, -1, 2*R0*R1, 0, -R0*R1*R1];
    let ρ0s = solve_quartic(c0);
    let ρ1s = solve_quartic(c1);
    ρs = [
      ρ0s.map(ρ0 => [ρ0, 1 - R0*ρ0*ρ0]),
      ρ1s.map(ρ1 => [1 - R1*ρ1*ρ1, ρ1]),
      ρ0s.flatMap(ρ0 => ρ1s.map(ρ1 => {
        //console.log(ρ0 - (1 - R1*ρ1*ρ1), ρ1 - (1 - R0*ρ0*ρ0));
        return [ρ0, ρ1];
      })),
    ][0];
    //console.log(ρs);
    δs = ρs.map(([ρ0,ρ1]) => [ρ0 * axd1 / d0xd1, ρ1 * d0xa / d0xd1]);
    /*/
    let c0 = [axd1*d0xd1*d0xd1 - (3/2)*k1*d0xa*d0xa, -d0xd1*d0xd1*d0xd1, (9/2)*k1*k0*d0xa, 0, -(27/8)*k1*k0*k0];
    let c1 = [d0xa*d0xd1*d0xd1 - (3/2)*k0*axd1*axd1, -d0xd1*d0xd1*d0xd1, (9/2)*k1*k0*axd1, 0, -(27/8)*k1*k0*k0];
    let δ0s = solve_quartic(c0);
    let δ1s = solve_quartic(c1);
    δs = [
      δ0s.map(δ0 => [δ0, (d0xa - (3/2)*k0*δ0*δ0)/d0xd1]),
      δ1s.map(δ1 => [(axd1 - (3/2)*k1*δ1*δ1)/d0xd1, δ1]),
      δ0s.flatMap(δ0 => δ1s.map(δ1 => {
        console.log(δ0 - (axd1 - (3/2)*k1*δ1*δ1)/d0xd1, δ1 - (d0xa - (3/2)*k0*δ0*δ0)/d0xd1);
        return [δ0, δ1];
      })),
    ][2];
    δs = δs.filter(([δ0,δ1]) => δ0 >= 0 && δ1 >= 0);
    /**/
  }
  return δs.map(([δ0,δ1]) => [f0,add(f0, mul(δ0, d0)),sub(f1, mul(δ1, d1)),f1]);
};
const fit_existing = P => {
  return fit(P[0], P[3], sub(P[1], P[0]), sub(P[3], P[2]), Bcurvature0(P), Bcurvature1(P));
};
const fit_existing_score = P => {
  let Qs = fit_existing(P);
  return Qs.map(Q => ({
    P, Q,
    P0: Bcurvature0(P), P1: Bcurvature1(P),
    Q0: Bcurvature0(Q), Q1: Bcurvature1(Q),
  }));
}

const degree = cs => {
  var d = 0;
  for (let i in cs) {
    if (cs[i]) d = +i;
  }
  return d;
};

const solve = eq => {
  var d = degree(eq);
  if (d === 0) {
    if (eq[0]) return [];
    return null; // everything is a solution
  } else if (d === 1) {
    return [-eq[0]/eq[1]];
  } else if (d === 2) {
    var disc = eq[1]*eq[1] - 4*eq[2]*eq[0];
    if (disc < 0) return [];
    if (disc === 0) return -eq[1]/eq[2]/2;
    var r = Math.sqrt(disc);
    return [+r,-r].map(sr => (-eq[1] + sr)/eq[2]/2);
  }
  throw new Error("Cannot solve equation of degree " + d);
};
const solve_norm = eq => solve_norm_sgn(eq)[0];
const solve_norm_sgn = eq => {
  var sols = solve(eq);
  if (sols.length === 0) {
    var disc = eq[1]*eq[1] - 4*eq[2]*eq[0];
    throw new Error("No solutions to " + eq + " with disc = " + disc);
  }
  var norm_sols = sols.filter(t => 0 <= t && t <= 1);
  if (norm_sols.length === 1) {
    return [norm_sols[0], [+1, -1][sols.findIndex(t => t == norm_sols[0])]];
  }
  throw new Error("Solutions were " + sols + " (to " + eq + ")");
};
const solve_deriv = (eq, dq) => {
  if (degree(eq) > 2) throw Error(eq);
  let [q, sgn] = solve_norm_sgn(eq);
  return (dq[2]*q*q + dq[1]*q + dq[0])/(2*eq[2]*q + eq[1]);
  let disc = sgn*Math.sqrt(eq[1]*eq[1] - 4*eq[2]*eq[0]);
  let n = eq[1]*dq[1] - 2*dq[2]*eq[0] - 2*eq[2]*dq[0];
  console.log([-dq[1]/eq[0]/2, n/disc/eq[0], -dq[2]*q/eq[0]]);
  return -dq[1]/eq[0]/2 + n/disc/eq[0] - dq[2]*q/eq[0];
};
const solve_deriv_ = (eq, dq) => {
  return [ -1e-3, -1e-4, -1e-5, -1e-6, -1e-7, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3 ].map(dp => {
    return (solve_norm(eq) - solve_norm(add(mul(dp, dq), eq)))/dp;
  });
};

const T_THINGY = (P,Q) => {
  var PP = DERIV(B(P));
  var QQ = transpose(DERIV(B(Q)));
  return PP.map(cd => {
    return sub(mul(cd[0], QQ[1]), mul(cd[1], QQ[0]));
  });
};
// PP : p :: QQ : q
// QQ_x(q)*PP_y(p) - QQ_y(q)*PP_x(p) = 0
const T_IMPLICIT = (P,Q) => {
  var PP = transpose(DERIV(B(P)));
  var QQ = transpose(DERIV(B(Q)));
  return sub(dmul(QQ[1], PP[0]), dmul(QQ[0], PP[1]));
};
const T_SOL = (P,Q) => p => solve_norm(values(T_IMPLICIT(P,Q))(p));
const T_DERIV = (P,Q) => p => {
  // multivariate polynomial in q,p
  let EQ = T_IMPLICIT(P,Q);
  // quadratic equation for q at p
  let eq = values(EQ)(p);
  // derivative of eq
  let dq = values(EQ.map(deriv))(p);
  return solve_deriv(eq, dq);
};
// c.T_DERIVS(c.ex.P, c.ex.Q)(0.36657)
const T_DERIVS = (P,Q) => p => {
  var q = T_SOL(P,Q)(p);
  return [ -1e-3, -1e-4, -1e-5, -1e-6, -1e-7, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3 ].map(dp => {
    return (q - T_SOL(P,Q)(dp+p))/dp;
  });
};
const PQ_CURVATURE = (P,Q) => p => {
  let q = T_SOL(P,Q)(p);
  let PP = DERIV(B(P));
  let QQ = DERIV(B(Q));
  let PPp = EVAL(PP)(p);
  let QQq = EVAL(QQ)(q);
  let PPPp = EVAL(DERIV(PP))(p);
  let QQQq = EVAL(DERIV(QQ))(q);
  let R = T_DERIV(P,Q)(p);
  let XX = PPp[0] + QQq[0]*R;
  let YY = PPp[1] + QQq[1]*R;
  let XXXYY = PPPp[0]*PPp[1] + PPPp[0]*QQq[1]*R + QQQq[0]*R*R*PPp[1] + QQQq[0]*QQq[1]*R*R*R;
  let YYYXX = PPPp[1]*PPp[0] + PPPp[1]*QQq[0]*R + QQQq[1]*R*R*PPp[0] + QQQq[1]*QQq[0]*R*R*R;
  let speed = Math.pow(XX*XX + YY*YY, 3/2);
  return (XXXYY - YYYXX)/speed;
  /*
  (x''y' - y''x')/((x'2 + y'2)^3/2)
  */
};
const T_VERIFY = (P,Q) => (p, q) => value(values(T_IMPLICIT(P,Q))(p))(q === undefined ? T_SOL(P,Q)(p) : q);
const T_VERIFY2 = (P,Q) => (p, q) => value(values(T_IMPLICIT(Q,P))(q === undefined ? T_SOL(P,Q)(p) : q))(p);
const T_VERIFYT = (P,Q) => (p, q) => {
  if (p === undefined) q = T_SOL(P,Q)(p);
  var PPp = EVAL(DERIV(B(P)))(p);
  var TPp = PPp[1]/PPp[0];
  var QQq = EVAL(DERIV(B(Q)))(q);
  var TQq = QQq[1]/QQq[0];
  return [ TPp, TQq, TPp - TQq ];
};
const T_VERIFY3 = (P,Q) => (p, q) => {
  if (q === undefined) q = T_SOL(P,Q)(p);
  return [ T_VERIFY, T_VERIFY2, T_VERIFYT ].map(f => f(P,Q)(p, q));
};

//const T_DERIV = ;

module.exports = {
  zipWith, add, sub, mul, compose, transpose, dot, lift1, lift2, map, value, deriv, N, Y, b, B, bases,
  muldot, summate, sum, DERIV, EVAL, values, dmul,
  transposing, transposed,
  solve_norm, solve, solve_deriv, solve_deriv_,
  T_IMPLICIT, T_SOL, T_VERIFY, T_VERIFY2, T_VERIFYT, T_VERIFY3,
  T_DERIV, T_DERIVS,
  curvature, Bcurvature, Bcurvature_polys, Bcurvature0, Bcurvature1,
  fit, fit_existing, fit_existing_score,
  raise, pmul, norm, normalize,
  Vec, Poly, Curve, curveD,
  ex: (function() {
    let r = {};
    try {
      r.P = curveD([[7,6],[4,2],[1,2],[5,1]]);
      r.PP = transpose(DERIV(B(r.P)));
      r.Q = curveD([[1,3],[4,5],[6,7],[1,3]]);
      r.QQ = transpose(DERIV(B(r.Q)));
      r.t = 0.4;
      r.tt = T_SOL(r.P, r.Q)(r.t);
    } catch (e) {
      console.log(e);
    }
    return r;
  })(),
};
