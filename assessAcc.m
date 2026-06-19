%%%%%%%%%%%%%
%
% Tester of model to separate pairs of points
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem 
%
%%%%%%%%%%%%%

function acc = assessAcc(net, setT1, setT2)
% assessAcc calculates accuracy of separation pairs of points (fraction of
% separated pairs).
%
% Inputs:
%   model is network or other model which produced normal vector. This
%       model has dim inputs and outputs, where dim is dimension of space.
%   setT1, setT2 are pairs of vectors for training set. Each pair is used
%   for separation point from the secons subset from corresponding point
%   from the first subset.
%
%   acc is calculated accuracy.

    % Calculate normals
    normT = predict(net, setT2);
    % Calculate dot products of difference of two vectors by normals
    resT = sum((setT1 - setT2) .* normT, 2);
    acc = 1 - sum(resT >= 0) / size(setT1, 1);
end

