%%%%%%%%%%%%%%%
%
% Generate data for empirical calculations
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%%%

% Five arrays are generated:
% 1. trSets1 - training set 1 - is the set of the first vectors in pairs
% 2. trSets2 - training set 2 - is the set of the second vectors in pairs
% 3. valSets1 - validation set 1 - is the set of the first vectors in pairs
% 4. valSets2 - validation set 2 - is the set of the second vectors in pairs
% 5. Test set is the set of points to select sets of different cardinality
%
% Object with parameters for calculation of the best theoretical direction
% is also stored with data. If mu is not used then use mu = 1;


distribs = ["Cauchy", "Cube", "Exp", "Gauss", "Laplace", "Pareto"];

% Specify number of distribution. If you want to add new distribution, you
% should add distribution's name to distribs and add generation below
dists = 5; 

distr = distribs(dists);

% File name for generated data
fileToSave = distr +"\" + distr + "AllData.mat";
% Number of pairs of points in the train set or 
% Number of pairs of points in the validation set 
trSize = 50000;
% number of points in the test set 
setSize = 100000;
% All points have dimension maxDim. Points od smaller dimension dim are
% extracted by taking coordinates from 1 to dim.
maxDim = 100;

% Just in case
mu = 1;

switch dists
    case 1
        % Cauchy
        trSets1 = trnd(1, trSize , maxDim);
        trSets2 = trnd(1, trSize , maxDim);
        valSets1 = trnd(1, trSize , maxDim);
        valSets2 = trnd(1, trSize , maxDim);
        testSet = trnd(1, setSize , maxDim);
    case 2
        % Cube
        trSets1 = 2 * rand(trSize, maxDim) - 1;
        trSets2 = 2 * rand(trSize, maxDim) - 1;
        valSets1 = 2 * rand(trSize, maxDim) - 1;
        valSets2 = 2 * rand(trSize, maxDim) - 1;
        testSet = 2 * rand(setSize, maxDim) - 1;
        % Load approximation of c(x) function
        load(distr + "/TheBestForCube.mat", "c", "X");
        mu = struct("x", X, "c", c);
    case 3
        % Exp
        trSets1 = exprnd(mu, trSize, maxDim) - 1;
        trSets2 = exprnd(mu, trSize, maxDim) - 1;
        valSets1 = exprnd(mu, trSize, maxDim) - 1;
        valSets2 = exprnd(mu, trSize, maxDim) - 1;
        testSet = exprnd(mu, setSize, maxDim) - 1;
    case 4
        % Gauss
        trSets1 = randn(trSize, maxDim);
        trSets2 = randn(trSize, maxDim);
        valSets1 = randn(trSize, maxDim);
        valSets2 = randn(trSize, maxDim);
        testSet = randn(setSize, maxDim);
    case 5
        % Laplace
        trSets1 = 0.5 * exprnd(1, trSize, maxDim);
        tmp = rand(trSize, maxDim);
        ind = tmp < 0.5;
        trSets1(ind) = -trSets1(ind);
        trSets2 = 0.5 * exprnd(1, trSize, maxDim);
        tmp = rand(trSize, maxDim);
        ind = tmp < 0.5;
        trSets2(ind) = -trSets2(ind);
        valSets1 = 0.5 * exprnd(1, trSize, maxDim);
        tmp = rand(trSize, maxDim);
        ind = tmp < 0.5;
        valSets1(ind) = -valSets1(ind);
        valSets2 = 0.5 * exprnd(1, trSize, maxDim);
        tmp = rand(trSize, maxDim);
        ind = tmp < 0.5;
        valSets2(ind) = -valSets2(ind);
        testSet = randn(setSize, maxDim);
        tmp = rand(setSize, maxDim);
        ind = tmp < 0.5;
        testSet(ind) = -testSet(ind);
    case 6
        % Pareto
        m = [1, 1]; % x_m and \gamma
        trSets1 = gprnd(1 / m(2), m(1) / m(2), m(2), trSize, maxDim);
        trSets2 = gprnd(1 / m(2), m(1) / m(2), m(2), trSize, maxDim);
        valSets1 = gprnd(1 / m(2), m(1) / m(2), m(2), trSize, maxDim);
        valSets2 = gprnd(1 / m(2), m(1) / m(2), m(2), trSize, maxDim);
        testSet = gprnd(1 / m(2), m(1) / m(2), m(2), setSize, maxDim);
        % Load approximation of c(x) function
        load(distr + "/TheBestForPareto.mat", "c", "X");
        mu = struct("x", X, "c", c);
end

save(fileToSave, "trSets1", "trSets2", "valSets1", "valSets2", "mu", "testSet");