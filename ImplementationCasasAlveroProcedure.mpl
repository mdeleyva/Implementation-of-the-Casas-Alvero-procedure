with(combinat);
with(ArrayTools);
with(Groebner);
with(plottools);
with(plots);
with(ListTools);
with(GraphTheory);
	
enQ := proc(Ddeg, GLTdeg) local encima, i;
	encima := false;
	for i in GLTdeg do
		if i[1] <= Ddeg[1][1] and i[2] <= Ddeg[1][2] then
			encima := true;
			return encima;
		end if;
	end do;
	return encima;
end proc;

Rfinal := proc(n, m, R) local Rf, monR, mr;
	Rf := R;
	if type(R, `+`) then
		monR := [op(R)];
	else
		monR := [R];
	end if;
	for mr in monR do
		if n*(m - 1) + m*(n - 1) + 1 < n*degree(mr, x) + m*degree(mr, y) then
			Rf := Rf - mr;
		end if;
	end do;
	return Rf;
end proc;

estrella := proc(G, GLT, GLTdeg, GLTcoeff) local n, comb, estrella, i, gcdmon, g, g1deg, g2deg;
	n := numelems(G);
	comb := choose(n, 2);
	estrella := [];
	for i in comb do
		g1deg := x^GLTdeg[i[1]][1]*y^GLTdeg[i[1]][2];
		g2deg := x^GLTdeg[i[2]][1]*y^GLTdeg[i[2]][2];
		gcdmon := gcd(g1deg, g2deg);
		g := GLTcoeff[i[2]]*g2deg*G[i[1]]/gcdmon - GLTcoeff[i[1]]*g1deg*G[i[2]]/gcdmon;
		g := micollect(g);
		estrella := [op(estrella), g];
	end do;
	return estrella;
end proc;

initialform := proc(n, m, f) local listf, degrees, elem, cox, coy, twi, minimal, posi, pos, auxil;
	listf := convert(f, list, `+`);
	degrees := [];
	for elem in listf do
		cox := degree(elem, x);
		coy := degree(elem, y);
		twi := n*cox + m*coy;
		degrees := [op(degrees), twi];
	end do;
	minimal := FindMinimalElement(degrees);
	posi := SearchAll(minimal, degrees);
	auxil := 0;
	for pos in posi do
		auxil := auxil + listf[pos];
	end do;
	return auxil;
end proc;

micollect := proc(f) local listf, finalf, elem, co, deg, faux;
	faux := f;
	faux := collect(faux, [x, y], 'distributed');
	listf := convert(faux, list, `+`);
	finalf := 0;
	for elem in listf do
		co := coeffs(collect(elem, [x, y], 'distributed'), [x, y]);
		co := simplify(co, size);
		deg := [degree(elem, x), degree(elem, y)];
		finalf := co*x^deg[1]*y^deg[2] + finalf;
	end do;
	finalf := collect(finalf, [x, y], 'distributed');
	return finalf;
end proc;

eqncheck := proc(eqns, sol) local numeqns, check, i, solucionar, evaluar;
	numeqns := numelems(eqns);
	check := true;
	for i to numeqns do
		try evaluar := eval(eqns[i], sol);
			solucionar := solve(evaluar);
			catch: print('En*la*primera*rama*hay*una*división*entre*cero');
			solucionar := NULL;
		end try;
		if solucionar = NULL then
			return false;
		end if;
	end do;
	return check;
end proc;

esc := proc(n, m, G) local escfinal, numG, i, ini;
	escfinal := [];
	numG := numelems(G);
	for i to numG do
		ini := initialform(n, m, G[i]);
		escfinal := [op(escfinal), [degree(ini, x), degree(ini, y)]];
	end do;
	return escfinal;
end proc;

esc2 := proc(n, m, G) local escfinal, numG, i, ini;
	escfinal := [];
	numG := numelems(G);
	for i to numG do
		ini := initialform(n, m, G[i]);
		escfinal := [op(escfinal), ini];
	end do;
	return escfinal;
end proc;

division := proc(n, m, div, IFdivdeg, IFdivcoeff, G, IFGdeg, IFGcoeff) local nIFdiv, nIFG, resto, i, fuera, dentroQ, j, xmayor, ymayor, resta;
	nIFdiv := numelems(IFdivdeg);
	nIFG := numelems(IFGdeg);
	resto := div;
	for i to nIFdiv do
		fuera := n*(m - 1) + m*(n - 1) + 1 < n*IFdivdeg[i][1] + m*IFdivdeg[i][2];
		dentroQ := enQ(IFdivdeg, IFGdeg);
		if fuera or not dentroQ then
			return [false, resto];
		end if;
		for j to nIFG do
			xmayor := 0 <= IFdivdeg[i][1] - IFGdeg[j][1];
			ymayor := 0 <= IFdivdeg[i][2] - IFGdeg[j][2];
			if xmayor and ymayor then
				resta := IFdivcoeff[i]*G[j]*x^(IFdivdeg[i][1] - IFGdeg[j][1])*y^(IFdivdeg[i][2] - IFGdeg[j][2])/IFGcoeff[j];
				resto := resto - resta;
				resto := micollect(resto);
				break;
			end if;
		end do;
	end do;
	return [true, resto];
end proc;

paso := proc(n, m, div, IFdivdeg, IFdivcoefff, G, IFGdeg, IFGcoeff) local pasodivision, resto, divisible, IFresto, nIFresto, IFrestodeg, IFrestocoeff, i;
	pasodivision := division(n, m, div, IFdivdeg, IFdivcoefff, G, IFGdeg, IFGcoeff);
	divisible := pasodivision[1];
	resto := pasodivision[2];
	while divisible do
		IFresto := initialform(n, m, resto);
		IFresto := micollect(IFresto);
		if type(IFresto, `+`) then
			IFresto := [op(IFresto)];
		else
			IFresto := [IFresto];
		end if;
		nIFresto := numelems(IFresto);
		IFrestodeg := [];
		IFrestocoeff := [];
		for i to nIFresto do
			IFrestodeg := [op(IFrestodeg), [degree(IFresto[i], x), degree(IFresto[i], y)]];
			f := [op(IFrestocoeff), coeffs(collect(IFresto[i], [x, y], 'distributed'), [x, y])];
		end do;
		pasodivision := division(n, m, resto, IFrestodeg, IFrestocoeff, G, IFGdeg, IFGcoeff);
		divisible := pasodivision[1];
		resto := pasodivision[2];
	end do;
	resto := Rfinal(n, m, resto);
	return resto;
end proc;

iteracion := proc(n, m, G, IFG, IFGdeg, IFGcoeff) local nG, convoluciones, nconvoluciones, todocero, IFconv, nIFconv, IFconvdeg, IFconvcoeff, i, Resto, Restodeg, j, k, Restoaux, IFRestoaux, IFRestoauxdeg, menortwisteddeg;
	convoluciones := estrella(G, IFG, IFGdeg, IFGcoeff);
	nconvoluciones := numelems(convoluciones);
	todocero := true;
	IFconv := initialform(n, m, convoluciones[1]);
	IFconv := micollect(IFconv);
	if type(IFconv, `+`) then
		IFconv := [op(IFconv)];
	else
		IFconv := [IFconv];
	end if;
	nIFconv := numelems(IFconv);
	IFconvdeg := [];
	IFconvcoeff := [];
	for i to nIFconv do
		IFconvdeg := [op(IFconvdeg), [degree(IFconv[i], x), degree(IFconv[i], y)]];
		IFconvcoeff := [op(IFconvcoeff), coeffs(collect(IFconv[i], [x, y], 'distributed'), [x, y])];
	end do;
	Resto := paso(n, m, convoluciones[1], IFconvdeg, IFconvcoeff, G, IFGdeg, IFGcoeff);
	if Resto = 0 then
		Restodeg := [infinity, infinity];
	else
		Restodeg := [degree(Resto, x), degree(Resto, y)];
	end if;
	for j from 2 to nconvoluciones do
		IFconv := initialform(n, m, convoluciones[j]);
		IFconv := micollect(IFconv);
		if type(IFconv, `+`) then
			IFconv := [op(IFconv)];
		else
			IFconv := [IFconv];
		end if;
		nIFconv := numelems(IFconv);
		IFconvdeg := [];
		IFconvcoeff := [];
		for k to nIFconv do
			IFconvdeg := [op(IFconvdeg), [degree(IFconv[k], x), degree(IFconv[k], y)]];
			IFconvcoeff := [op(IFconvcoeff), coeffs(collect(IFconv[k], [x, y], 'distributed'), [x, y])];
		end do;
		Restoaux := paso(n, m, convoluciones[j], IFconvdeg, IFconvcoeff, G, IFGdeg, IFGcoeff);
		if Restoaux <> 0 then
			todocero := false;
			IFRestoaux := initialform(n, m, Restoaux);
			IFRestoaux := micollect(IFRestoaux);
			IFRestoauxdeg := [degree(IFRestoaux, x), degree(IFRestoaux, y)];
			menortwisteddeg := n*IFRestoauxdeg[1] + m*IFRestoauxdeg[2] < n*Restodeg[1] + m*Restodeg[2];
			if menortwisteddeg then
				Resto := Restoaux;
				Restodeg := IFRestoauxdeg;
			end if;
		end if;
	end do;
	return [todocero, Resto];
end proc;

main1 := proc(n, m, f, contNodos, Nodos, Aristas, Ley, nodo, HE, lastcoeff, eqns) local G, IFG, IFGdeg, IFGcoeff, IFf, IFfdeg, IFfcoeff, g3, IFg3, pasoalgoritmo, todocero, g, IFg, IFgcoeff, contNodosaux, Nodosaux, Aristasaux, Leyaux, HEaux, nodoaux;
	contNodosaux := contNodos;
	Nodosaux := Nodos;
	Aristasaux := Aristas;
	Leyaux := Ley;
	HEaux := HE;
	nodoaux := nodo;
	if f = 0 then
		print('Resultado*rama*igual*a*cero');
		print([false, false]);
		return [false, false];
	end if;
	G := [diff(f, x), diff(f, y)];
	IFG := [initialform(n, m, G[1]), initialform(n, m, G[2])];
	IFGdeg := [[degree(IFG[1], x), degree(IFG[1], y)], [degree(IFG[2], x), degree(IFG[2], y)]];
	IFGcoeff := [coeffs(collect(IFG[1], [x, y], 'distributed'), [x, y]), coeffs(collect(IFG[2], [x, y], 'distributed'), [x, y])];
	IFf := initialform(n, m, f);
	IFf := [op(IFf)];
	IFfdeg := [[degree(IFf[1], x), degree(IFf[1], y)], [degree(IFf[2], x), degree(IFf[2], y)]];
	IFfcoeff := [coeffs(collect(IFf[1], [x, y], 'distributed'), [x, y]), coeffs(collect(IFf[2], [x, y], 'distributed'), [x, y])];
	g := paso(n, m, f, IFfdeg, IFfcoeff, G, IFGdeg, IFGcoeff);
	if g = 0 then
		contNodosaux := contNodosaux + 1;
		Nodosaux := [op(Nodosaux), N[contNodosaux]];
		Aristasaux := Aristasaux union {[nodo, N[contNodosaux]]};
		Leyaux := [op(Leyaux), N[contNodosaux] = 'End'];
		HEaux := [op(HEaux), {N[contNodosaux], nodo}];
		print('Resultado*rama*igual*a*cero');
		print('End');
		return [false, G, contNodosaux, Nodosaux, Aristasaux, Leyaux, N[contNodosaux], HEaux];
	else
		G := [op(G), g];
		IFg := initialform(n, m, g);
		IFgcoeff := coeffs(collect(IFg, [x, y], 'distributed'), [x, y]);
		IFG := [op(IFG), IFg];
		IFGdeg := [op(IFGdeg), [degree(IFg, x), degree(IFg, y)]];
		IFGcoeff := [op(IFGcoeff), coeffs(collect(IFg, [x, y], 'distributed'), [x, y])];
		while type(IFgcoeff, 'complexcons') or member(IFgcoeff <> 0, eqns) do
			if type(IFgcoeff, 'complexcons') then
				contNodosaux := contNodosaux + 1;
				Nodosaux := [op(Nodosaux), N[contNodosaux]];
				Aristasaux := Aristasaux union {[nodoaux, N[contNodosaux]]};
				Leyaux := [op(Leyaux), N[contNodosaux] = IFg];
				nodoaux := N[contNodosaux];
			end if;
			pasoalgoritmo := iteracion(n, m, G, IFG, IFGdeg, IFGcoeff);
			todocero := pasoalgoritmo[1];
			g := pasoalgoritmo[2];
			if todocero then
				contNodosaux := contNodosaux + 1;
				Nodosaux := [op(Nodosaux), N[contNodosaux]];
				Aristasaux := Aristasaux union {[nodoaux, N[contNodosaux]]};
				Leyaux := [op(Leyaux), N[contNodosaux] = 'End'];
				HEaux := [op(HEaux), {N[contNodosaux], nodoaux}];
				print('Resultado*rama*igual*a*cero');
				print('End');
				return [false, G, contNodosaux, Nodosaux, Aristasaux, Leyaux, N[contNodosaux], HEaux];
			end if;
			G := [op(G), g];
			IFg := initialform(n, m, g);
			IFgcoeff := coeffs(collect(IFg, [x, y], 'distributed'), [x, y]);
			IFG := [op(IFG), IFg];
			IFGdeg := [op(IFGdeg), [degree(IFg, x), degree(IFg, y)]];
			IFGcoeff := [op(IFGcoeff), coeffs(collect(IFg, [x, y], 'distributed'), [x, y])];
		end do;
		contNodosaux := contNodosaux + 1;
		Nodosaux := [op(Nodosaux), N[contNodosaux]];
		Aristasaux := Aristasaux union {[nodoaux, N[contNodosaux]]};
		Leyaux := [op(Leyaux), N[contNodosaux] = IFg];
		HEaux := [op(HEaux), {N[contNodosaux], nodoaux}];
		print('Resultado*rama*igual*a*cero');
		print(IFg);
		return [G, IFg, contNodosaux, Nodosaux, Aristasaux, Leyaux, N[contNodosaux], HEaux];
	end if;
end proc;

main2 := proc(n, m, f, nG, contNodos, Nodos, Aristas, Ley, nodo, lastcoeff, eqns) local G, IFG, IFGdeg, IFGcoeff, IFf, IFfdeg, IFfcoeff, g3, IFg3, pasoalgoritmo, todocero, g, nsig, IFg, IFgcoeff, contNodosaux, Nodosaux, Aristasaux, Leyaux, i, nodoaux, HEaux;
	contNodosaux := contNodos;
	Nodosaux := Nodos;
	Aristasaux := Aristas;
	Leyaux := Ley;
	nodoaux := nodo;
	if f = 0 then
		print('Resultado*rama*distinto*de*cero');
		print([false, false]);
		return [false, false];
	end if;
	G := [diff(f, x), diff(f, y)];
	IFG := [initialform(n, m, G[1]), initialform(n, m, G[2])];
	IFGdeg := [[degree(IFG[1], x), degree(IFG[1], y)], [degree(IFG[2], x), degree(IFG[2], y)]];
	IFGcoeff := [coeffs(collect(IFG[1], [x, y], 'distributed'), [x, y]), coeffs(collect(IFG[2], [x, y], 'distributed'), [x, y])];
	IFf := initialform(n, m, f);
	IFf := [op(IFf)];
	IFfdeg := [[degree(IFf[1], x), degree(IFf[1], y)], [degree(IFf[2], x), degree(IFf[2], y)]];
	IFfcoeff := [coeffs(collect(IFf[1], [x, y], 'distributed'), [x, y]), coeffs(collect(IFf[2], [x, y], 'distributed'), [x, y])];
	g := paso(n, m, f, IFfdeg, IFfcoeff, G, IFGdeg, IFGcoeff);
	if g = 0 then
		contNodosaux := contNodosaux + 1;
		Nodosaux := [op(Nodosaux), N[contNodosaux]];
		Aristasaux := Aristasaux union {[nodo, N[contNodosaux]]};
		Leyaux := [op(Leyaux), N[contNodosaux] = 'End'];
		HEaux := [op(HEaux), {N[contNodosaux], nodo}];
		print('Resultado*rama*igual*a*cero');
		print('End');
		return [false, G, contNodosaux, Nodosaux, Aristasaux, Leyaux, N[contNodosaux], HEaux];
	else
		G := [op(G), g];
		IFg := initialform(n, m, g);
		IFG := [op(IFG), IFg];
		IFGdeg := [op(IFGdeg), [degree(IFg, x), degree(IFg, y)]];
		IFGcoeff := [op(IFGcoeff), coeffs(collect(IFg, [x, y], 'distributed'), [x, y])];
		for i from 4 to nG + 1 do
			pasoalgoritmo := iteracion(n, m, G, IFG, IFGdeg, IFGcoeff);
			todocero := pasoalgoritmo[1];
			g := pasoalgoritmo[2];
			if todocero then
				contNodosaux := contNodosaux + 1;
				Nodosaux := [op(Nodosaux), N[contNodosaux]];
				Aristasaux := Aristasaux union {[nodo, N[contNodosaux]]};
				Leyaux := [op(Leyaux), N[contNodosaux] = 'End'];
				print('Resultado*rama*distinto*de*cero');
				print('End');
				return [false, G, contNodosaux, Nodosaux, Aristasaux, Leyaux, N[contNodosaux]];
			else
				G := [op(G), g];
				IFg := initialform(n, m, g);
				IFgcoeff := coeffs(collect(IFg, [x, y], 'distributed'), [x, y]);
				IFG := [op(IFG), IFg];
				IFGdeg := [op(IFGdeg), [degree(IFg, x), degree(IFg, y)]];
				IFGcoeff := [op(IFGcoeff), coeffs(collect(IFg, [x, y], 'distributed'), [x, y])];
			end if;
		end do;
		while type(IFgcoeff, 'complexcons') or member(IFgcoeff <> 0, eqns) do
			if type(IFgcoeff, 'complexcons') then
				contNodosaux := contNodosaux + 1;
				Nodosaux := [op(Nodosaux), N[contNodosaux]];
				Aristasaux := Aristasaux union {[nodoaux, N[contNodosaux]]};
				Leyaux := [op(Leyaux), N[contNodosaux] = IFg];
				nodoaux := N[contNodosaux];
			end if;
			pasoalgoritmo := iteracion(n, m, G, IFG, IFGdeg, IFGcoeff);
			todocero := pasoalgoritmo[1];
			g := pasoalgoritmo[2];
			if todocero then
				contNodosaux := contNodosaux + 1;
				Nodosaux := [op(Nodosaux), N[contNodosaux]];
				Aristasaux := Aristasaux union {[nodoaux, N[contNodosaux]]};
				Leyaux := [op(Leyaux), N[contNodosaux] = 'End'];
				print('Resultado*rama*distinto*de*cero');
				print('End');
				return [false, G, contNodosaux, Nodosaux, Aristasaux, Leyaux, N[contNodosaux]];
			end if;
			G := [op(G), g];
			IFg := initialform(n, m, g);
			IFgcoeff := coeffs(collect(IFg, [x, y], 'distributed'), [x, y]);
			IFG := [op(IFG), IFg];
			IFGdeg := [op(IFGdeg), [degree(IFg, x), degree(IFg, y)]];
			IFGcoeff := [op(IFGcoeff), coeffs(collect(IFg, [x, y], 'distributed'), [x, y])];
		end do;
		contNodosaux := contNodosaux + 1;
		Nodosaux := [op(Nodosaux), N[contNodosaux]];
		Aristasaux := Aristasaux union {[nodoaux, N[contNodosaux]]};
		Leyaux := [op(Leyaux), N[contNodosaux] = IFg];
		print('Resultado*rama*distinto*de*cero');
		print(IFg);
	end if;
	return [G, IFg, contNodosaux, Nodosaux, Aristasaux, Leyaux, N[contNodosaux]];
end proc;

rama := proc(n, m, var, f, G, IFg, freduc, eqns, contNodos, Nodos, Aristas, Ley, nodo, HE) local f1, f2, IFgcoeff, IFgdeg, xIFgdeg, yIFgdeg, irrelevantes, i, j, eqns1, eqns2, ramas, incog, soluciones, s, nsoluciones, auxf1, rama1, G1, IFg1, nG, rama2, G2, IFg2, contNodosaux, Nodosaux, Aristasaux, Leyaux, HEaux;
	contNodosaux := contNodos;
	Nodosaux := Nodos;
	Aristasaux := Aristas;
	Leyaux := Ley;
	HEaux := HE;
	if G = false then
		print('caso*G*es*false');
		return [[false, false, f]];
	end if;
	print('Nodo');
	print(IFg);
	f1 := freduc;
	f2 := freduc;
	IFgcoeff := coeffs(collect(IFg, [x, y], 'distributed'), [x, y]);
	IFgdeg := [degree(IFg, x), degree(IFg, y)];
	xIFgdeg := IFgdeg[1];
	yIFgdeg := IFgdeg[2];
	eqns1 := [op(eqns), IFgcoeff = 0];
	eqns2 := [op(eqns), IFgcoeff <> 0];
	ramas := [];
	incog := indets(IFgcoeff);
	soluciones := {solve(IFgcoeff, var)};
	print('Rama*igual*a*cero');
	print(soluciones);
	for s in soluciones do
		nsoluciones := numelems(soluciones);
		if 1 < nsoluciones then
			print('En*la*primera*rama*hay*varias*soluciones');
		end if;
		auxf1 := f1;
		if eqncheck(eqns, s) then
			try auxf1 := eval(auxf1, s);
				catch: auxf1 := 0;
				print('En*la*primera*rama*hay*una*división*entre*cero');
			end try;
			rama1 := main1(n, m, auxf1, contNodosaux, Nodosaux, Aristasaux, Leyaux, nodo, HEaux, IFgcoeff, eqns);
			G1 := rama1[1];
			IFg1 := rama1[2];
			contNodosaux := rama1[3];
			Nodosaux := rama1[4];
			Aristasaux := rama1[5];
			Leyaux := rama1[6];
			HEaux := rama1[8];
			ramas := [op(ramas), [G1, IFg1, auxf1, eqns1, rama1[7]]];
		else
			print('False;-1;asumimos*lo*contrario*antes;');
		end if;
	end do;
	print('esto*es*Ge');
	print(G);
	nG := numelems(G);
	rama2 := main2(n, m, f2, nG, contNodosaux, Nodosaux, Aristasaux, Leyaux, nodo, IFg, eqns);
	G2 := rama2[1];
	IFg2 := rama2[2];
	contNodosaux := rama2[3];
	Nodosaux := rama2[4];
	Aristasaux := rama2[5];
	Leyaux := rama2[6];
	ramas := [op(ramas), [G2, IFg2, f2, eqns2, rama2[7]]];
	return ramas, [contNodosaux, Nodosaux, Aristasaux, Leyaux, HEaux];
end proc;

escalera := proc(n, m, ivalues, jvalues) local plotfinal, ivaluesaux, jvaluesaux, ll, iminaux, imin, iminpos, jmin, imin2aux, imin2, imin2pos, jmin2;
	plotfinal := [display(line([0, n], [0, n - 1], color = "Orange", thickness = 4)), display(line([m - 1, 0], [m, 0], color = "Orange", thickness = 4))];
	ivaluesaux := ivalues;
	jvaluesaux := jvalues;
	ll := numelems(ivaluesaux);
	while 1 < ll do
		iminaux := FindMinimalElement(ivaluesaux, position);
		imin := iminaux[1];
		iminpos := iminaux[2];
		jmin := jvaluesaux[iminpos];
		ivaluesaux := subsop(iminpos = NULL, ivaluesaux);
		jvaluesaux := subsop(iminpos = NULL, jvaluesaux);
		imin2aux := FindMinimalElement(ivaluesaux, position);
		imin2 := imin2aux[1];
		imin2pos := imin2aux[2];
		jmin2 := jvaluesaux[imin2pos];
		plotfinal := [op(plotfinal), display(line([imin, jmin], [imin2, jmin], color = "Orange", thickness = 4)), display(line([imin2, jmin], [imin2, jmin2], color = "Orange", thickness = 4))];
		ll := numelems(ivaluesaux);
	end do;
	return plotfinal;
end proc;

punto := proc(n, m, ivalue, ivalues, jvalues) local ivaluesaux, jvaluesaux, ivaluesord, ivaluepos, ivalueant, ivaluesig, ivalueposant, ivaluepossig, iant, jant, jvalue, isig, jsig, punto1, punto2, punto, ivalueposord;
	ivaluesaux := ivalues;
	jvaluesaux := jvalues;
	ivaluesord := sort(ivaluesaux);
	ivaluepos := Search(ivalue, ivaluesaux);
	ivalueposord := Search(ivalue, ivaluesord);
	ivalueant := ivaluesord[ivalueposord - 1];
	ivaluesig := ivaluesord[ivalueposord + 1];
	ivalueposant := Search(ivalueant, ivaluesaux);
	ivaluepossig := Search(ivaluesig, ivaluesaux);
	iant := ivaluesaux[ivalueposant];
	jant := jvaluesaux[ivalueposant];
	jvalue := jvaluesaux[ivaluepos];
	isig := ivaluesaux[ivaluepossig];
	jsig := jvaluesaux[ivaluepossig];
	punto1 := [ivalue, jant];
	punto2 := [isig, jvalue];
	punto := punto1;
	if punto2[1]*n + punto2[2]*m < punto1[1]*n + punto1[2]*m then
		punto := punto2;
	end if;
	return punto;
end proc;

rosa := proc(n, m, G) local ivalues, i, j, jvalues, plot1, plot2, GLT, iGLTdeg, jGLTdeg, plot3, plot4, pto, plot5, esc, lista, plotfinal, numG, p, valuesrosa, GLTdeg, r, b, puntosrosa, irosa, jrosa;
	ivalues := [];
	jvalues := [];
	valuesrosa := [];
	puntosrosa := [];
	irosa := [];
	jrosa := [];
	for i from 0 to m - 2 do
		for j from 0 to n - 2 do
			if m*n < n*i + m*j then
				ivalues := [op(ivalues), i];
				jvalues := [op(jvalues), j];
				valuesrosa := [op(valuesrosa), [i, j]];
			end if;
		end do;
	end do;
	iGLTdeg := [degree(G[1], x), degree(G[2], x)];
	jGLTdeg := [degree(G[1], y), degree(G[2], y)];
	GLTdeg := [[degree(G[1], x), degree(G[1], y)], [degree(G[2], x), degree(G[2], y)]];
	plotfinal := [plot(Vector(ivalues), Vector(jvalues), x = 0 .. m, y = 0 .. m, axis = [gridlines = [linestyle = dot]], style = point, symbol = asterisk, color = "Black"), plot((m*n - n*x)/m, x = 0 .. m, y = 0 .. m, axis = [gridlines = [linestyle = dot]], color = "Black"), display(line([0, n - 1], [m - 1, n - 1], color = "Grey")), display(line([m - 1, n - 1], [m - 1, 0], color = "Grey"))];
	numG := numelems(G);
	for p from 3 to numG do
		iGLTdeg := [op(iGLTdeg), degree(G[p], x)];
		jGLTdeg := [op(jGLTdeg), degree(G[p], y)];
		GLTdeg := [op(GLTdeg), [degree(G[p], x), degree(G[p], y)]];
		pto := punto(n, m, iGLTdeg[p], iGLTdeg, jGLTdeg);
		for r in valuesrosa do
			if not enQ([r], GLTdeg) and n*iGLTdeg[p] + m*jGLTdeg[p] < n*r[1] + m*r[2] and n*r[1] + m*r[2] < n*pto[1] + m*pto[2] then
				puntosrosa := [op(puntosrosa), r];
				irosa := [op(irosa), r[1]];
				jrosa := [op(jrosa), r[2]];
			end if;
		end do;
		plotfinal := [op(plotfinal), plot((n*pto[1] + m*pto[2] - n*x)/m, x = 0 .. m, y = 0 .. m, axis = [gridlines = [linestyle = dot]], color = "Yellow"), plot((n*iGLTdeg[p] + m*jGLTdeg[p] - n*x)/m, x = 0 .. m, y = 0 .. m, axis = [gridlines = [linestyle = dot]], color = "Blue")];
	end do;
	esc := escalera(n, m, iGLTdeg, jGLTdeg);
	lista := [op(esc), op(plotfinal), plot(Vector(iGLTdeg), Vector(jGLTdeg), x = 0 .. m, y = 0 .. m, axis = [gridlines = [linestyle = dot]], style = point, symbol = solidcircle, color = "Blue"), plot(Vector(irosa), Vector(jrosa), x = 0 .. m, y = 0 .. m, axis = [gridlines = [linestyle = dot]], style = point, symbol = solidcircle, color = "Magenta")];
	print(plots:-display(lista));
	return puntosrosa, numelems(puntosrosa);
end proc;

tjurina := proc(n, m, G) local numG, Gdeg, elemG, iG, jG, t;
	numG := numelems(G);
	Gdeg := [];
	t := 0;
	for elemG to numG do
		Gdeg := [op(Gdeg), [degree(G[elemG], x), degree(G[elemG], y)]];
	end do;
	for iG from 0 to m do
		for jG from 0 to n do
			if not enQ([[iG, jG]], Gdeg) then
				t := t + 1;
			end if;
		end do;
	end do;
	return t;
end proc;

jacobiano := proc(n, m, escalera) local jacobiano, nescalera, i, jacaux;
	jacobiano := [0, m - n];
	nescalera := numelems(escalera);
	for i from 3 to nescalera do
		jacaux := n*escalera[i][1] + m*escalera[i][2] - m*n + m;
		(jacobiano), jacaux];
	end do;
	return jacobiano;
end proc;

main := proc(n, m, f, var) local freduc, G, IFG, IFGdeg, IFGcoeff, IFf, IFfdeg, IFfcoeff, g3, IFg3, pasoalgoritmo, todocero, g, IFg, ramas, nramas, ramasaux, ramasterminadas, terminadas, i, nuevarama, nr, ramasfinal, escalonfinal, nramasterminadas, j, Greduc, numfinal1, k, ntjurina, nrosas, Nodos, Aristas, eqns, contNodos, Ley, nodo, pasorama, infoGrafo, Grafo, STGrafo, HE, jacaux, escaux;
	contNodos := 1;
	Nodos := [N[1]];
	Aristas := {};
	Ley := [];
	HE := [];
	freduc := f;
	G := [diff(f, x), diff(f, y)];
	IFG := [initialform(n, m, G[1]), initialform(n, m, G[2])];
	IFGdeg := [[degree(IFG[1], x), degree(IFG[1], y)], [degree(IFG[2], x), degree(IFG[2], y)]];
	IFGcoeff := [coeffs(collect(IFG[1], [x, y], 'distributed'), [x, y]), coeffs(collect(IFG[2], [x, y], 'distributed'), [x, y])];
	IFf := initialform(n, m, f);
	IFf := [op(IFf)];
	IFfdeg := [[degree(IFf[1], x), degree(IFf[1], y)], [degree(IFf[2], x), degree(IFf[2], y)]];
	IFfcoeff := [coeffs(collect(IFf[1], [x, y], 'distributed'), [x, y]), coeffs(collect(IFf[2], [x, y], 'distributed'), [x, y])];
	g3 := paso(n, m, f, IFfdeg, IFfcoeff, G, IFGdeg, IFGcoeff);
	IFg3 := initialform(n, m, g3);
	eqns := [];
	nodo := N[1];
	Ley := [op(Ley), N[1] = IFg3];
	pasorama := rama(n, m, var, f, G, IFg3, freduc, eqns, contNodos, Nodos, Aristas, Ley, nodo, HE);
	ramas := pasorama[1];
	infoGrafo := pasorama[2];
	contNodos := pasorama[2][1];
	Nodos := pasorama[2][2];
	Aristas := pasorama[2][3];
	Ley := pasorama[2][4];
	HE := pasorama[2][5];
	nramas := numelems(ramas);
	ramasaux := [];
	ramasterminadas := [];
	while 0 < nramas do
		for i to nramas do
			if ramas[i][1] = false then
				if not (ramas[i][2] = false) then
					ramasterminadas := [op(ramasterminadas), [ramas[i][2], ramas[i][3], ramas[i][4], esc(n, m, ramas[i][2]), ramas[i][5]]];
				end if;
			else
				pasorama := rama(n, m, var, f, ramas[i][1], ramas[i][2], ramas[i][3], ramas[i][4], contNodos, Nodos, Aristas, Ley, ramas[i][5], HE);
				nuevarama := pasorama[1];
				infoGrafo := pasorama[2];
				contNodos := pasorama[2][1];
				Nodos := pasorama[2][2];
				Aristas := pasorama[2][3];
				Ley := pasorama[2][4];
				HE := pasorama[2][5];
				for nr in nuevarama do
					if nr[1] = false then
						if not (nr[2] = false) then
							ramasterminadas := [op(ramasterminadas), [nr[2], nr[3], nr[4], esc(n, m, nr[2]), nr[5]]];
						end if;
					else
						ramasaux := [op(ramasaux), nr];
					end if;
				end do;
			end if;
		end do;
		ramas := ramasaux;
		nramas := numelems(ramas);
		ramasaux := [];
	end do;
	nramasterminadas := numelems(ramasterminadas);
	Grafo := Graph(Nodos, Aristas);
	STGrafo := SpanningTree(Grafo);
	HighlightEdges(STGrafo, HE, stylesheet = [color = "Red", thickness = 2]);
	print(DrawGraph(STGrafo));
	printf("Esta es la leyenda del grafo");
	print(Ley);
	for j to nramasterminadas do
		printf("Esta es la escalera %a", j);
		print(ramasterminadas[j][4]);
		printf("Estos son los valores del jacobiano %a", j);
		jacaux := jacobiano(n, m, ramasterminadas[j][4]);
		print(jacaux);
		printf("Este es el nodo %a", j);
		print(ramasterminadas[j][5]);
		printf("Estas son las initial forms de la escalera %a", j);
		Greduc := esc2(n, m, ramasterminadas[j][1]);
		print(Greduc);
		numfinal1 := numelems(ramasterminadas[j][1]);
		for k to numfinal1 do
			printf("Esto es g %a", k);
			print(ramasterminadas[j][1][k]);
		end do;
		printf("Esta es la ecuación final %a", j);
		print(ramasterminadas[j][2]);
		printf("Estas son las ecuaciones %a", j);
		print(ramasterminadas[j][3]);
		printf("Este es el número de Tjurina %a", j);
		ntjurina := tjurina(n, m, Greduc);
		print(ntjurina);
		printf("Este es el diagrama de puntos rosas %a", j);
		nrosas := rosa(n, m, Greduc);
		printf("Este es el número de puntos rosas %a", j);
		print(nrosas[2]);
	end do;
	return 'Ya*es*el*final';
end proc;

posibleszariskis := proc(n, m) local expzariskis, valzariskis, zariskis, variables, i, j, pasosort, valzariskisorden, nvalzariskisorden, k, auxvariables;
	expzariskis := [];
	valzariskis := [];
	zariskis := [];
	variables := [];
	auxvariables := [];
	for i to m - 2 do
		for j to n - 2 do
			if m*n < n*i + m*j then
				auxvariables := [op(auxvariables), _EnvA[i, j]];
				expzariskis := [op(expzariskis), [i, j]];
				valzariskis := [op(valzariskis), n*i + m*j - m*n];
			end if;
		end do;
	end do;
	pasosort := sort(valzariskis, output = [sorted, permutation]);
	valzariskis := pasosort[1];
	valzariskisorden := pasosort[2];
	nvalzariskisorden := numelems(valzariskisorden);
	for k to nvalzariskisorden do
		zariskis := [op(zariskis), [expzariskis[valzariskisorden[k]], valzariskis[k]]];
		variables := [op(variables), auxvariables[valzariskisorden[k]]];
	end do;
	return [zariskis, variables];
end proc;

ecuacion := proc(n, m, zariskis, variables) local f, nvariables, j;
	f := y^n - x^m;
	nvariables := numelems(variables);
	for j to nvariables do
		f := f + variables[j]*x^zariskis[j][1][1]*y^zariskis[j][1][2];
	end do;
	return f;
end proc;

inic := proc(n, m) local variables, mainaux, zariskis, ec;
	zariskis := posibleszariskis(n, m)[1];
	variables := posibleszariskis(n, m)[2];
	ec := ecuacion(n, m, zariskis, variables);
	variables := convert(variables, set);
	printf("Esta es la ecuación inicial");
	print(ec);
	printf("Aquí empiezan los cálculos");
	mainaux := main(n, m, ec, variables);
	return 'Final';
end proc;

inic(5, 12);




NULL;