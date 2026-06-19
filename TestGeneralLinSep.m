%%%%%%%%%%%%%%%
%
% Test general linear separability based on linear programming
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%%%

distribs = ["Cauchy", "Cube", "Exp", "Gauss", "Laplace", "Pareto"];

% Specify number of distribution. If you want to add new distribution, you
% should add distribution's name to distribs and add corresponding blocks
% to some functions.

dists = 5;

% Required probability of separability
p = 0.99;

%%%%%%%%%%%%%%%
%
% Functions
%
%%%%%%%%%%%%%%%

function res = isConvex(data)
    N = size(data, 1);
    data = [data, ones(size(data, 1), 1)];
    f = zeros(N - 1, 1);
    lb = zeros(N - 1, 1);
    ub = ones(N - 1, 1);
    options = optimoptions('linprog', 'Display', 'none');
    for i = 1:N
        if i == 1 
            ind = 2:N;
        elseif i == N
            ind = 1:N - 1;
        else
            ind = [1:i - 1, i + 1:N];
        end
        [~, ~, exitflag] = linprog(f, [], [], data(ind, :)',...
            data(i, :)', lb, ub, options);
        if exitflag == 1
            res = false;
            return
        end
    end
    res = true;
end

function vals = testOneM(data, m, nTests)
    setSizes = size(data, 1);
    seps = 0;
    parfor t = 1:nTests
        ind = randperm(setSizes, m);
        sets = data(ind, :); %#ok<PFBNS>
        if ~isConvex(sets)
            seps = seps + 1;
        end
    end
    % Calculate statistics
    vals = 1 - seps / nTests;
end

% General constaants
dims = [5:15, 20:5:80]';
nDim = length(dims);
nTests = 10000;
maxSize = 75000;

% Cauchy Cube Exp Gauss Laplace Pareto

distr = distribs(dists);

% Load data
load(distr + "/" + distr + "AllData.mat", "testSet");
saveFile = distr + "/LinSep_%d.mat";

% Next dimension has at least the same cardinality as previous one.
lastCard = 1;

for d = 1:nDim
    % data for test
    dim = dims(d);
    
    tstSet = testSet(:, 1:dim);

    % File name for work
    fNameRes = sprintf(saveFile, dim);
    
    if isfile(fNameRes)
        load(fNameRes)
        fprintf("Load dimension %d cardinality %d probability %.3f\n", ...
            dim, mypool(end, :));
    else
        if lastCard == 1
            lastCard = dim + 2;
        end
        mypool = [lastCard, testOneM(tstSet, lastCard, nTests)];
        fprintf("Start dimension %d cardinality %d probability %.3f\n", ...
            dim, mypool);
        save(fNameRes, "mypool");
    end

    % Now we search minimal set to start data collection
    while mypool(1, 1) > 2 && mypool(1, 2:end) < p
        % Decrease by 10%
        q = round(mypool(1, 1) / 1.1);
        % Decreasing must be at least 1
        if q == mypool(1, 1)
            q = q - 1;
        end
        
        tmp = [q, testOneM(tstSet, q, nTests)];
        mypool = [tmp; mypool]; %#ok<AGROW>
        fprintf("Decreasing dimension %d cardinality %d probability %.3f\n", ...
            dim, tmp);
        save(fNameRes, "mypool");
    end

    % Search of the last m where probability is greater or equal to 0.99
    % for at least one of model
    while mypool(end, 1) < maxSize && mypool(end, 2:end) > p
        % Increase by 10%
        q = round(mypool(end, 1) * 1.1);
        % Increasing must be at least 1
        if q == mypool(end, 1)
            q = q + 1;
        end
        tmp = [q, testOneM(tstSet, q, nTests)];
        fprintf("Increase dimension %d cardinality %d probability %.3f\n", ...
            dim, tmp);
        mypool = [mypool; tmp]; %#ok<AGROW>
        save(fNameRes, "mypool");
    end
    lastCard = mypool(end, 1);
end
