%%%%%%%%%%%%%
%
% Implementation of subtraction layer
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%

classdef subtractionLayer < nnet.layer.Layer 
    methods
        function layer = subtractionLayer(names)
            % Set layer name
            layer.Name = char(names);
            % Set layer description
            layer.Description = "Quadratic activation function";
            % Allow to have two inputs
            layer.NumInputs = 2;
        end

        function Z = predict(~, X1, X2)
            % Forward input data through the layer at prediction time and
            % output the result
            Z = X1 - X2;
        end

        function [dLdX1, dLdX2] = backward(~, ~, ~, ~, dLdZ, ~)
            % Backward propagate the derivative of the loss function through 
            % the layer
            dLdX1 = dLdZ;
            dLdX2 = - dLdZ;
        end

    end
end