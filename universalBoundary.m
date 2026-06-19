%%%%%%%%%%%%%%%
%
% Function to calculate the values for universal boundary according to
% Corollary 5.7 of paper.
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%%%

function res = universalBoundary(dims, p)
% universalBoundary converts vector of dimensions dims into number of
% separable points according to universal formula in Corollary 5.7 of
% paper.  
%
% Inputs:
%   dims is vector of dimensions.
%   p is probability oof separability
%
% Output
%   res is normal vector (many vectors) for x.

    res = sqrt(1 - p) * ((1 / sqrt(0.85)) .^ dims);
end