
declare type IsoParam;
declare attributes IsoParam:
	// A list of valid pivots.
	Pivots,

	// A pointer to the current pivot.
	PivotPtr,

	// The free variables that parameterize the isotropic subspaces with
	//  respect to our current pivot.
	FreeVars,

	// The parameters for the free variables for the current pivot.
	Params,

	// A matrix whose rows correspond to the parameterized isotropic
	//  subspaces.
	IsotropicParam;
	
// A helper function for computing valid pivots.
function __pivots(n, aniso, k)
        // Base case.
        if k eq 1 then return [ [i] : i in [1..n-aniso] ]; end if;

        // Retrieve lower-dimensional maximal pivots.
        pivots1 := __pivots(n-2, aniso, k-1);
        pivots1 := [ [ x+1 : x in data ] : data in pivots1 ];

        // Determine the first set of pivots.
        pivots1 := [ [1] cat data : data in pivots1 ] cat
                [ data cat [n-aniso] : data in pivots1 ];

        // Add additional pivots when we're not in the maximal case.
        if 2*k lt n-aniso then
                pivots2 := __pivots(n-2, aniso, k);
                pivots2 := [ [ x+1 : x in data ] : data in pivots2 ];
                return pivots1 cat pivots2;
        end if;

        return pivots1;
end function;

intrinsic BuildQuadraticSpace(M::ModMatFldElt : Symbolic := true)
	-> ModTupFld[FldFin]
{ Builds the quadratic space associated to the supplied Gram matrix. }
	M := Matrix(BaseRing(M), Nrows(M), Ncols(M), Eltseq(M));
	return BuildQuadraticSpace(M : Symbolic := Symbolic);
end intrinsic;

// Construct the quadratic space that we'll use to compute all isotropic liens.
intrinsic BuildQuadraticSpace(M::AlgMatElt[FldFin] : Symbolic := true)
	-> ModTupFld[FldFin]
{ Builds the quadratic space associated to the supplied Gram matrix. }
	// The quadratic space.
	V := QuadraticSpace(M);

	// Make sure we're in dimension 3 or higher.
	require Dimension(V) ge 2: "Dimension must be 3 or greater.";

	// Assign the Gram matrix.
	V`GramMatrix := M;

	// Decompose the form into a standard form (R + H + A).
	V`GramMatrixStd, V`Basis := Decompose(M);

	// Count the rows at the end of the matrix which are exactly zero.
	idx := Dimension(V);
	while idx ge 1 and V`GramMatrixStd[idx] eq Zero(V) do
		idx -:= 1;
	end while;

	// The dimension of the radical.
	V`RadDim := Dimension(V) - idx;

	// Determine the dimension of the totally hyperbolic subspace.
	idx := 1;
	while idx le Dimension(V)-V`RadDim and V`GramMatrixStd[idx,idx] eq 0 do
		idx +:= 1;
	end while;

	// Dimension of the anistotropic subspace.
	V`AnisoDim := Dimension(V) - V`RadDim - idx + 1;

	// The number of hyperbolic planes in the Witt decomposition.
	V`WittIndex := Integers()!((idx-1)/2);

	// Assign the multinomial of the quadratic form.
	if Characteristic(BaseRing(M)) ne 2 then
		V`Q := QuadraticForm(M / 2);
		V`QStd := QuadraticForm(V`GramMatrixStd / 2);
	else
		V`Q := QF2(M);
		V`QStd := QF2(V`GramMatrixStd);
	end if;

	// Assign an ordering to the elements of the finite field.
	V`S := [ 0 ] cat [ x : x in BaseRing(M) | x ne 0 ];

	// Create an empty parameterization array.
	V`ParamArray := AssociativeArray();

	// Set symbolic flag.
	V`Symbolic := Symbolic;

	// Assign the cyclic generator of the group of units of the field.
	V`PrimitiveElement := PrimitiveElement(BaseRing(M));

	return V;
end intrinsic;

procedure __initializePivot(V, k)
	// Retrieve parameters for this dimension.
	data := V`ParamArray[k];

	// The current pivot.
	pivot := data`Pivots[data`PivotPtr];

	// The base field.
	F := BaseRing(V);

	// Multivariant polynomial ring used to determine parameterization.
	R := PolynomialRing(F, k * Dimension(V));

	// Initialize matrix that will determine parameterization.
	M := Matrix(R, k, Dimension(V), [ R.i : i in [1..Rank(R)] ]);

	// Keep a list of non-free variables from which we will determine the
	//  free variables when we are done.
	remove := [];

	// Setup the columns corresponding to the pivots.
	for i in [1..k], j in [1..k] do
		M[i,pivot[j]] := i eq j select 1 else 0;
		Append(~remove, (i-1)*Dimension(V) + pivot[j]);
	end for;

	// Clear the rows prior to the pivot positions (but not the radical).
	for i in [1..k], j in [1..pivot[i]-1] do
		M[i,j] := 0;
		Append(~remove, (i-1)*Dimension(V) + j);
	end for;

	// Check if one or more of the anisotropic coordinates need to be zero.
	for i in [1..k] do
		if pivot[i] gt V`WittIndex then
			for j in [1..V`AnisoDim] do
				M[i,Dimension(V)+1-V`RadDim-j] := 0;
				Append(~remove, i*Dimension(V)+1-V`RadDim-j);
			end for;
		end if;
	end for;

	// Determine the number of rows of the matrix that we'll echelonize.
	rows := Integers()!(k*(k+1)/2);
	cols := Rank(R) + 1;

	// The field of fractions of the polynomial ring.
	RF := FieldOfFractions(R);

	// The matrix that we're going to echelonize.
	mat := Matrix(RF, rows, cols, [ 0 : i in [1..rows*cols] ]);

	// The current row to fill in in the matrix.
	row := 1;

	for i in [1..k], j in [i..k] do
		// The appropriate vector that we want to be isotropic.
		vec := i eq j select M[i] else M[i]+M[j];

		// Multinomial corresponding to the i-th basis vector.
		f := Evaluate(V`QStd, Eltseq(vec));

		// Check each term of the resulting multinomial.
		for term in Terms(f) do
			if Degree(term) eq 2 then
				// Degree 2 terms are inhomogenous.
				mat[row][cols] -:= term;
			else
				// Otherwise we have a linear term.
				val, mono := Contpp(term);
				coord := &+[ mono eq R.n select n else 0
					: n in [1..Rank(R)] ];

				// And so fill in the matrix accordingly.
				mat[row,coord] := val;
			end if;
		end for;

		// Move on to the next row.
		row +:= 1;
	end for;

	// Compute the Echelon form of the matrix.
	E := EchelonForm(mat);

	// The evaluation list for replacing variables with their dependence
	//  relations.
	list := [* R.i : i in [1..Rank(R)] *];

	for i in [1..Nrows(E)] do
		// Find the pivot in the i-th row.
		c := 0; repeat c +:= 1;
		until c gt Rank(R)+1 or E[i][c] eq 1;

		// Add this pivot to the list of non-free variables.
		Append(~remove, c);

		// If the pivot is equal to Rank(R)+1, we have a problem.
		assert c ne Rank(R)+1;

		// If the row is entirely zero, skip it.
		if c gt Rank(R)+1 then continue; end if;

		// Build the multinomial for which R.c is dependent.
		f := E[i][Rank(R)+1];
		for j in [ l : l in [1..Rank(R)] | l ne c ] do
			f -:= E[i][j] * R.j;
		end for;
		list[c] := f;
	end for;

	// The matrix whose rows parameterize all isotropic subspaces.
	M := Evaluate(M, [ l : l in list ]);

	// Verify that we didn't screw up somewhere along the line.
	for i in [1..k], j in [i..k] do
		vec := i eq j select M[i] else M[i]+M[j];
		assert Evaluate(V`QStd, Eltseq(vec)) eq 0;
	end for;

	// Determinen the free variables.
	data`FreeVars := [ n : n in [1..Rank(R)] | not n in remove ];

	// The parameterization vector for this pivot.
	data`Params := [* 0 : i in [1..#data`FreeVars] *];

	// Assign the parameterization of the isotropic subspaces.
	data`IsotropicParam := M;
end procedure;

intrinsic FirstIsotropicSubspace(V::ModTupFld[FldFin], k::RngIntElt) -> SeqEnum
{ Returns the first non-singular isotropic subspace. }
	// Make sure the requested dimension is valid.
	require k ge 1: "Requested isotropic dimension must be at least 1.";

	// Parameters for this dimension not yet initialized, so create a new
	//  entry in the catalog.
	if not IsDefined(V`ParamArray, k) then
		data := New(IsoParam);
		data`Pivots := __pivots(Dimension(V) - V`RadDim, V`AnisoDim, k);
		V`ParamArray[k] := data;
	end if;

	// Reset the pivot pointer and subspace parameters.
	V`ParamArray[k]`PivotPtr := 0;
	V`ParamArray[k]`Params := [];

	// Return the first isotropic subspace.
	return NextIsotropicSubspace(V, k);
end intrinsic;

intrinsic NextIsotropicSubspace(V::ModTupFld[FldFin], k::RngIntElt) -> SeqEnum
{ Returns the next non-singular isotropic subspace. }
	// Make sure the requested dimension is valid.
	require k ge 1: "Requested isotropic dimension must be at least 1.";

	// If isotropic subspaces of this dimension haven't been initialized,
	//  then treat it as if we were requesting the first isotropic subspace.
	if not IsDefined(V`ParamArray, k) then
		data := New(IsoParam);
		data`Pivots := __pivots(Dimension(V) - V`RadDim, V`AnisoDim, k);
		data`PivotPtr := 0;
		data`Params := [];
		V`ParamArray[k] := data;
	end if;

	// Retrieve the parameters for the requested dimension.
	data := V`ParamArray[k];

	// Check to see if we need to initialize a new pivot.
	if #data`Params eq 0 then
		// Move to the next pivot.
		data`PivotPtr +:= 1;

		// If we've exceeded the list of pivots, we're done.
		if data`PivotPtr gt #data`Pivots then
			// Reset the pivot pointer so that we can loop through
			//  the isotropic subspaces again if needed.
			data`PivotPtr := 0;
			return [];
		end if;

		// Initialize the new pivot.
		__initializePivot(V, k);
	end if;

	// The dimension of the isotropic subspace we're constructing.
	k := #data`Pivots[data`PivotPtr];

	// The list of evaluation values.
	evalList := [* 0 : i in [1..Dimension(V)*k] *];

	// Produce the isotropic subspace corresponding to the current
	//  parameters.
	for i in [1..#data`Params] do
		if V`Symbolic then
			evalList[data`FreeVars[i]] := V`S[data`Params[i]+1];
		else
			evalList[data`FreeVars[i]] := data`Params[i];
		end if;
	end for;

	// The basis for the current isotropic subspace.
	space := Rows(Evaluate(data`IsotropicParam, [ x : x in evalList]));

	if #data`FreeVars ne 0 then
		// The current position in the parameterization.
		pos := 0;

		// Terminate loop once we found the next new subspace, or we
		//  hit the end of the list.
		repeat
			// Increment position.
			pos +:= 1;

			if V`Symbolic then
				// Increment value.
				data`Params[pos] +:= 1;

				// Check to see if we've rolled over.
				if (data`Params[pos] mod #V`S) eq 0 then
					// Reset value if so.
					data`Params[pos] := 0;
				end if;
			else
				// Manually move to the next element.
				if IsPrime(#BaseRing(V)) then
					data`Params[pos] +:= 1;
				elif data`Params[pos] eq 0 then
					data`Params[pos] := V`PrimitiveElement;
				elif data`Params[pos] eq 1 then
					data`Params[pos] := 0;
				else
					data`Params[pos] *:= V`PrimitiveElement;
				end if;
			end if;
		until pos eq #data`FreeVars or data`Params[pos] ne 0;
	end if;

	// If we've hit the end of the list, indicate we need to move on to the
	//  next pivot.
	if &and[ x eq 0 : x in data`Params ] then data`Params := []; end if;

	return space;
end intrinsic;

intrinsic AllIsotropicSubspaces(V::ModTupFld[FldFin], k::RngIntElt) -> SeqEnum
{ Returns an array consisting of all isotropic vectors. }
	// TODO: Relax this condition to allow for higher dimensional spaces.
	require k eq 1: "Must be one dimensional subspaces currently.";

	// The first isotropic subspace.
	space := FirstIsotropicSubspace(V, k);

	// The list of isotropic subspaces.
	list := [];

	while space ne [] do
		// Retrieve the isotropic subspace in the original coordinates.
		vec := Vector(Matrix(space[1]) * Transpose(V`Basis));

		// Normalize the isotropic vector.
		pos := 0;
		repeat pos +:= 1;
		until vec[pos] ne 0;

		// Add to list.
		//Append(~list, vec / vec[pos]);
		Append(~list, sub< V | vec >);

		// Next subspace.
		space := NextIsotropicSubspace(V, k);
	end while;

	return list;
end intrinsic;

intrinsic IsotropicSubspaces(V::ModTupFld[FldFin], k::RngIntElt) -> SeqEnum
{ Counts all isotropic subspace. }
	// The first isotropic subspace.
	space := FirstIsotropicSubspace(V, k);

	// The isotropic subspace counter.
	count := 0;

	while space ne [] do
		// Increment counter.
		count +:= 1;

		// Move on to the next subspace.
		space := NextIsotropicSubspace(V, k);
	end while;

	// Return the count.
	return count;
end intrinsic;

intrinsic NumberOfIsotropicSubspaces(M::ModFrmAlg, p::RngIntElt, k::RngIntElt)
	-> RngIntElt
{ Determine the number of isotropic subspaces. }
	return NumberOfIsotropicSubspaces(M, ideal< Integers() | p >, k);
end intrinsic;

intrinsic NumberOfIsotropicSubspaces(M::ModFrmAlg, pR::RngInt, k::RngIntElt)
	-> RngIntElt
{ Determine the number of isotropic subspaces. }
	// Consider the rationals as a number field.
	K := RationalsAsNumberField();

	// The ring of integers as an order.
	R := Integers(K);

	// Compute via the master intrinsic.
	return NumberOfIsotropicSubspaces(M, ideal< R | Norm(pR) >, k);
end intrinsic;

intrinsic NumberOfIsotropicSubspaces(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt)
	-> RngIntElt
{ Determine the number of isotropic subspaces. }
	// Make sure that the dimension is valid.
	require k ge 1:
		"Isotropic subspaces must have positive dimension.";

	// Verify that the ideal is prime.
	require IsPrime(pR): "Specified ideal must be prime.";

	// Compute the residue class field.
	F := ResidueClassField(pR);

	// The cardinality of the residue class field.
	q := #F;

	// The underlying quadratic space.
	Q := QuadraticSpace(Module(M));

	// The dimension of the quadratic space.
	n := Dimension(Q);

	// An auxiliary integer used in our formulas.
	m := Integers()!( n mod 2 eq 1 select (n-1)/2 else n/2 );

	// Compute the number of isotropic subspaces.
	if n mod 2 eq 1 then
		count := &*[ q^(2*(m-i+1))-1 : i in [1..k] ] /
			&*[ q^i-1 : i in [1..k] ];
	elif IsSquare(F!-1) then
		if m eq k then
			count := 2 * &*[ q^(2*(k-i))-1 : i in [1..k-1] ] /
				&*[ q^i-1 : i in [1..k-1] ];
		else
			count := (q^m-1) * &*[ q^(2*(m-i))-1 : i in [1..k] ] /
				(q^(m-k)-1) / &*[ q^i-1 : i in [1..k] ];
		end if;
	else
		e := IsEven(m+1) select 1 else -1;
		if m eq k then
			count := 2 * &*[ q^(2*(k-i))-1 : i in [1..k-1] ] *
				(q^k+e) / (q^k-1) / &*[ q^i-1 : i in [1..k-1] ];
		else
			count := (q^m+e) * &*[ q^(2*(m-i))-1 : i in [1..k] ] /
				(q^(m-k)+e) / &*[ q^i-1 : i in [1..k] ];
		end if;
	end if;

	// Verify that this count is an integer.
	assert Denominator(count) eq 1;

	return Integers()!count;
end intrinsic;

intrinsic NumberOfNeighbors(M::ModFrmAlg, p::RngIntElt, k::RngIntElt)
	-> RngIntElt
{ Determine the number of p^k-neighbor lattices. }
	return NumberOfNeighbors(M, ideal< Integers() | p >, k);
end intrinsic;

intrinsic NumberOfNeighbors(M::ModFrmAlg, pR::RngInt, k::RngIntElt)
	-> RngIntElt
{ Determine the number of p^k-neighbor lattices. }
	// Consider the rationals as a number field.
	K := RationalsAsNumberField();

	// The ring of integers as an order.
	R := Integers(K);

	return NumberOfNeighbors(M, ideal< R | Norm(pR) >, k);
end intrinsic;

intrinsic NumberOfNeighbors(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt)
	-> RngIntElt
{ Determine the number of p^k-neighbor lattices. }
	// Determine the number of isotropic subspaces.
	n := NumberOfIsotropicSubspaces(M, pR, k);

	// The size of the residue class field.
	q := #ResidueClassField(pR);

	// Compute the number of p^k-neighbors.
	return n * q^(Integers()!(k*(k-1)/2));
end intrinsic;
