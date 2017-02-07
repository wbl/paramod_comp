// Constructs a random symmetric matrix over a specified finite field of a specified dimension.
intrinsic RandomSymmetric(FF::Fld, dim::RngElt) -> Mtrx
{ Generate a random symmetric matrix of dimension Dim over a finite field FF. }
	M := RandomMatrix(FF, dim, dim);
	for j in [2..dim] do
		for k in [1..j-1] do
			M[j,k] := M[k,j];
		end for;
	end for;

	return M;
end intrinsic;

intrinsic RandomSymmetric(R::RngOrd, dim::RngIntElt, maxNorm::RngIntElt) -> AlgMatElt
{ Generates a random symmetric matrix over a ring. }
	M := Zero(MatrixRing(R, dim));

	for i in [1..dim] do
		for j in [i..dim] do
			repeat
				elt := R ! [ Random(-maxNorm,maxNorm) : x in [1..Degree(R)] ];
			until Norm(elt) le maxNorm;
			M[i,j] := elt;
			M[j,i] := elt;
		end for;
	end for;

	return M;
end intrinsic;

intrinsic RandomSymmetricInt(Dim::RngElt, Max::RngElt) -> Mtrx
{ Generates a random matrix over the integers with specified dimension, with maximal absolute entry. }
	R := MatrixRing(Integers(), Dim);

	repeat
		M := Zero(R);

		for i in [1..Dim] do
			num := Random(-Max, Max);
			M[i,i] := 2*num;
			for j in [i+1..Dim] do
				num := Random(-Max, Max);
				M[i,j] := num;
				M[j,i] := num;
			end for;
		end for;
	until IsPositiveDefinite(M);

	return M;
end intrinsic;

intrinsic RandomLattice(Dim::RngElt, Max::RngElt) -> Lat
{ Generates a random lattice with a gram matrix via the RandomSymmetricInt intrinsic. }
	return LatticeWithGram(RandomSymmetricInt(Dim, Max));
end intrinsic;

intrinsic QF2(M::AlgMatElt[RngOrdRes]) -> RngMPolElt
{}
	dim := Nrows(M);
	R := PolynomialRing(BaseRing(M), dim);
	Q := 0;
	for i in [1..dim] do
		for j in [i..dim] do
			Q +:= M[i,j] * R.j * R.i;
		end for;
	end for;
	return Q;
end intrinsic;

intrinsic QF2(M::AlgMatElt[FldFin]) -> RngMPolElt
{ Takes in a symmetric matrix over a field of characteristic 2 and constructs a multinomial corresponding to the quadratic form this matrix represents. }
	// Make sure the matrix is square.
	require Nrows(M) eq Ncols(M): "Supplied matrix must be square.";

	// Make sure the matrix is symmetric.
	require IsSymmetric(M): "Supplied matrix must be symmetric.";

	// Make sure the characteristic of the base ring is 2.
	require Characteristic(BaseRing(M)) eq 2:
		"Supplied matrix must be characteristic 2.";

	Dim := Nrows(M);
	R := PolynomialRing(BaseRing(M), Dim);
	Q := 0;
	for i in [1..Dim] do
		for j in [i..Dim] do
			Q +:= M[i,j] * R.j * R.i;
		end for;
	end for;

	return Q;
end intrinsic;

function MVM(M,v)
	return Vector(Transpose(M * Transpose(Matrix(v))));
end function;

