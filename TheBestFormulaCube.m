%%%%%%%%%%%%%
%
% Tabulate function c(x) for the best direction for uniform in cube
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%

% This script must be processed BEFORE data generation

function res = forMin(c, b)
    if c == 0
        res = 1;
    else
        res = exp(-c * b) * (exp(c) - 1) / c; 
    end
end

% Tabulation of function from minimum of function
X = -1:0.001:1;
b = X / 2 + 0.5;
c = zeros(size(X));
for k = 1:length(b)
    c(k) = fminbnd(@(x) forMin(x, b(k)), -1000, 1000);
end

save("Cube/TheBestForCube.mat", "c", "X");

